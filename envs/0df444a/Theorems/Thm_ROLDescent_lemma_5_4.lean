-- Prove2me | Theorems.Thm_ROLDescent_lemma_5_4
-- name    : ROLDescent.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:23.605701+00:00
-- url     : https://prove2.me/theorems/76597e2f-12f7-4c53-a702-e183f9a28592
-- title:
--   Lemma 5.4 — one-step Gram estimate $\theta\le F_\lambda(c^{\downarrow})$
-- statement:
--   Let $P$ be a connected reversible Markov matrix on a finite state space $N$ with at least two states and $P(i,i) = 0$, with stationary probabilities $\pi_i > 0$. Let $\mathcal U_i$ ($i \in N$) be subspaces of a finite-dimensional complex Hilbert space $\mathcal I$ with orthogonal projections $E_i$, and for each edge $P_{ij} > 0$ let $\mathcal B_{ij} = \mathcal B_{ji}$ be a subspace containing $\mathcal U_i + \mathcal U_j$. Put $\mathcal V_{ij} = \mathcal B_{ij} \cap \mathcal U_i^\perp$ and
--
--   $$c^{\downarrow} = \max_i \Big\| \sum_j P_{ij}\, \mathrm{Proj}_{\mathcal V_{ij}} \Big\|, \qquad \theta = \Big\| \sum_i \pi_i E_i \Big\| .$$
--
--   Assume $\bigcap_{i \in N} \mathcal U_i = \{0\}$, $\mathrm{gap}(\mathrm{id} - P) \ge \lambda > 0$ in $L^2(\pi)$, and $c^{\downarrow} < 1$.
--
--   Then
--
--   $$\theta \le F_\lambda(c^{\downarrow}) = \frac{(2 - \lambda)\, c^{\downarrow}}{\lambda (1 - c^{\downarrow})}.$$
--
--   In the hierarchy, $\theta$ is the parent Gram norm and $c^{\downarrow}$ the largest child Gram norm, so the lemma is the single step of the Gram recursion (79).
--
--   Differences from the source:
--   - encoding: P a connected reversible Markov matrix with stationary probabilities π_i > 0 → P ≥ 0 with rows summing to 1, P_ii = 0, π_i > 0 with Σπ_i = 1 and π_i P_ij = π_j P_ji, and the graph of the edges P_ij > 0 connected; reason: detailed balance and Σπ = 1 make π stationary; by connectivity it is the unique stationary law, so the instances are the same
--   - encoding: gap(id − P) ≥ λ in L²(π) → HDXConc.SecondEigLE on N with weights π_i P_ij and threshold 1 − λ (real test functions); reason: the weights have degrees π_i and walk P, which is self-adjoint in L²(π); Courant–Fischer
--   - encoding: sums over j with P_ij > 0; B_ij given only for edges → sums over all j; B : N → N → Submodule, constrained only where P_ij > 0; reason: terms with P_ij = 0 have coefficient 0
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Lemma 5.4, eq. (89), p.36 (PDF 36)

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_ROLDescent_gramUpdate

namespace ROLDescent

/-- **Lemma 5.4 (One-step Gram estimate).** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Lemma 5.4, eq. (89), p.36 (PDF 36): "In the
setting above, suppose that ⋂_{i∈N} U_i = {0}, gap(id − P) ≥ λ > 0 in L²(π), c↓ < 1. Then
θ ≤ F_λ(c↓) = (2 − λ)c↓ / (λ(1 − c↓))." The setting (p.36): "We now formulate the estimate for an abstract subspace configuration over a reversible
Markov chain. Let P be a connected reversible Markov matrix on a finite state space N with at
least two states, with P(i, i) = 0 as for the link walks defined above. Write π_i > 0 for its
stationary probabilities. Let U_i, i ∈ N, be linear subspaces of a finite-dimensional Hilbert
space I, with orthogonal projections E_i. For each edge P_ij > 0, let a linear subspace
B_ij = B_ji contain U_i + U_j. … Put V_ij := B_ij ∩ U_i^⊥, c↓ := max_i ‖Σ_j P_ij Proj_{V_ij}‖,
θ := ‖Σ_i π_i E_i‖, (88) where each sum over j runs over states j ∈ N with P_ij > 0."

**Formalization Note** The Hilbert space I is `E`. "Connected reversible Markov matrix" is: entries
`≥ 0`, rows summing to `1`, zero diagonal, detailed balance `π_i P_ij = π_j P_ji` with `π_i > 0`,
`Σ π_i = 1` (so `π` is stationary, and by connectivity the unique stationary law), and the graph of
the edges `P_ij > 0` connected. "gap(id − P) ≥ λ in L²(π)" is the public `HDXConc.SecondEigLE` with
weights `π_i P_ij` (degrees `π_i`, walk `P`) and threshold `1 − λ`. The sums over `j` run over all
states: terms with `P_ij = 0` carry coefficient `0`, and `B_ij` is unconstrained there. -/
theorem lemma_5_4 {N : Type*} [Fintype N] [DecidableEq N]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (P : N → N → ℝ) (π : N → ℝ) (U : N → Submodule ℂ E) (B : N → N → Submodule ℂ E) (lam : ℝ)
    (hcard : 2 ≤ Fintype.card N)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_row : ∀ i, ∑ j, P i j = 1) (hP_diag : ∀ i, P i i = 0)
    (hπ_pos : ∀ i, 0 < π i) (hπ_sum : ∑ i, π i = 1)
    (hrev : ∀ i j, π i * P i j = π j * P j i)
    (hconn : (SimpleGraph.fromRel (fun i j => 0 < P i j)).Connected)
    (hB : ∀ i j, 0 < P i j → B i j = B j i ∧ U i ⊔ U j ≤ B i j)
    (hU : (⨅ i, U i) = ⊥)
    (hgap : HDXConc.SecondEigLE Finset.univ (fun i j => π i * P i j) (1 - lam))
    (hlam : 0 < lam)
    (hc : (⨆ i, ‖∑ j, ((P i j : ℝ) : ℂ) • (B i j ⊓ (U i)ᗮ).starProjection‖) < 1) :
    ‖∑ i, ((π i : ℝ) : ℂ) • (U i).starProjection‖ ≤
      gramUpdate lam (⨆ i, ‖∑ j, ((P i j : ℝ) : ℂ) • (B i j ⊓ (U i)ᗮ).starProjection‖) := by sorry

end ROLDescent

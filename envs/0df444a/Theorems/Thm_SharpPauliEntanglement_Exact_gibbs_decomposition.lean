-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_gibbs_decomposition
-- name    : SharpPauliEntanglement.Exact.gibbs_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:14.643124+00:00
-- url     : https://prove2.me/theorems/ec135818-95fe-4619-8d76-94a5e1280564
-- title:
--   Proposition 3.2 — Exact Eq. (3.6) for arbitrary admissible shifts, plus its separability implication
-- statement:
--   Let $H=\sum_{i\in V}J_iP_i$ be a finite-qubit Pauli Hamiltonian, $\beta\ge0$, $z_i=\beta|J_i|$, and let $G$ be its term-overlap graph. Define $F_U,D_U$ by (3.1). For every nonempty connected set $\gamma$, choose any real shift $r_\gamma\ge\|D_\gamma\|_{P,1}$; put $R_\gamma=r_\gamma I+D_\gamma$ and define $Q_G$ by (3.5). Then
--
--   $$\frac{e^{-\beta H}}{\prod_{i\in V}\cosh z_i}=F_V=\sum_{\Gamma\text{ compatible}}Q_G\!\left(V\setminus N_G\!\left[\bigcup_{\gamma\in\Gamma}\gamma\right]\right)\prod_{\gamma\in\Gamma}R_\gamma.$$
--
--   If $Q_G(S)\ge0$ for every $S\subseteq V$, then $\rho_\beta(H)$ is a convex combination of product Pauli eigenprojectors. This is the arbitrary-shift decomposition, before the particular threshold activities are chosen. Empty families contribute the identity.
--
--   Differences from the source:
--   - encoding: arbitrary finite qubit and term labels → computational bitstrings and Fin n, Fin m labels; reason: finite reindexing preserves every matrix, support relation and source instance
--   - generalization: the nontrivial section regime has beta > 0 and m >= 1 → beta >= 0 and arbitrary m including zero; reason: the same finite expansion and normalized mixture statement remain valid at beta = 0 and for an empty Hamiltonian
--   - encoding: products over compatible polymers → products in an enumeration of each finite family; reason: the factors have disjoint supports and commute, so their order is immaterial
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 10, Proposition 3.2

import Definitions.Def_SharpPauliEntanglement_Exact_Polymers

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, pp. 9–10, Proposition 3.2, arbitrary shifts in (3.5).
The formula also includes the empty-Hamiltonian and β = 0 cases. -/
theorem gibbs_decomposition {n m : ℕ} (H : PauliHamiltonian (Fin n) (Fin m))
    (β : ℝ) (hβ : 0 ≤ β) (r : Finset (Fin m) → ℝ)
    (hr : ∀ γ : Finset (Fin m), ConnectedSet (overlapGraph H) γ →
      pauliNorm (inclusionExclusion H β γ) ≤ r γ) :
    ((∏ i, (Real.cosh (termZ H β i) : ℂ))⁻¹) •
        NormedSpace.exp ((-β : ℂ) • hamiltonian H) =
      normalizedExp H β Finset.univ ∧
    normalizedExp H β Finset.univ = polymerDecomposition H β r ∧
    ((∀ S : Finset (Fin m), 0 ≤ polymerPolynomial (overlapGraph H) r S) →
      PauliSeparable (gibbs (hamiltonian H) β)) := by sorry

end SharpPauliEntanglement.Exact

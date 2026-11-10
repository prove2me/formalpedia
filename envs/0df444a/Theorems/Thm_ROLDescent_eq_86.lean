-- Prove2me | Theorems.Thm_ROLDescent_eq_86
-- name    : ROLDescent.eq_86
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:26.082961+00:00
-- url     : https://prove2.me/theorems/e0d3afec-f7cb-487f-84dd-af0e43a74bcb
-- title:
--   Eq. (86) — nodewise energy bound $L_\tau\succeq\delta_\tau\,\mathrm{id}$ at every visited node
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d \ge 2$ whose link graphs with $m_\tau \ge 2$ are connected (the 1-skeleton of the link of every face with $|\tau| + 2 \le d$ is a connected graph), and let $(\mathcal I_\tau)$ be a subspace hierarchy (73) in a finite-dimensional complex Hilbert space $\mathcal K$. Write $\mathcal T_{\mathrm{int}}$ for the internal faces ($|\tau| \le d - 2$), $\mathcal T_{\mathrm{bot}}$ for those with $|\tau| = d - 2$, and $\mathcal T_{\mathrm{stop}}$ for the faces with $|\tau| = d - 1$. Take
--
--   1. bottom Gram bounds $\bar\theta_{\tau_\star}$ on $\mathcal T_{\mathrm{bot}}$ with $\theta_{\tau_\star} \le \bar\theta_{\tau_\star} < 1$ and $\bar\theta_{\tau_\star} \ge 0$ (78);
--   2. link-walk gap bounds $\lambda_\tau \in (0, 2]$ with $\mathrm{gap}(\mathrm{id} - P_\tau) \ge \lambda_\tau$ on $\mathcal T_{\mathrm{int}} \setminus \mathcal T_{\mathrm{bot}}$ (72);
--   3. the remaining Gram bounds defined by $\bar\theta_\tau = F_{\lambda_\tau}(c^\downarrow_\tau)$ with $c^\downarrow_\tau = \max_{i \in N_\tau} \bar\theta_{\tau i}$ (79), subject to $c^\downarrow_\tau < \lambda_\tau / 2$ (80), on $\mathcal T_{\mathrm{int}} \setminus \mathcal T_{\mathrm{bot}}$.
--
--   4. operators $L_\tau \succeq 0$ on $\mathcal I_\tau$ at every visited face, with energies $\mathcal E_\tau(b) = \langle b, L_\tau b\rangle$ satisfying the assembly inequality $\mathcal E_\tau(b) \ge \sum_{i \in N_\tau} \pi_\tau(i)\, \mathcal E_{\tau i}(\Pi_{\tau i} b)$ for $b \in \mathcal I_\tau$, $\tau \in \mathcal T_{\mathrm{int}}$ (81);
--   5. terminal bounds $\delta_\sigma > 0$ with $\mathcal E_\sigma(b) \ge \delta_\sigma \|b\|^2$ on $\mathcal T_{\mathrm{stop}}$ (82), extended to internal faces by $\delta_\tau = (1 - \bar\theta_\tau) \min_{i \in N_\tau} \delta_{\tau i}$ (83).
--
--   Then at every visited face $\tau$ (internal or stopping) and every $b \in \mathcal I_\tau$,
--
--   $$\mathcal E_\tau(b) = \langle b, L_\tau b\rangle \ge \delta_\tau \|b\|^2, \qquad \text{i.e. } L_\tau \succeq \delta_\tau\, \mathrm{id}_{\mathcal I_\tau}.$$
--
--   This is the energy transport step: terminal energy lower bounds travel to the root, losing the retention factor $1 - \bar\theta_\tau$ at each level.
--
--   Differences from the source:
--   - encoding: θ̄_τ defined recursively by (79) above T_bot → an input function θbar satisfying (79) as an equation on faces with τ.card + 3 ≤ d; reason: the recursion on d − |τ| determines θ̄ uniquely from the bottom bounds; same instances
--   - encoding: gap(id − P_τ) ≥ λ_τ in L²(π_τ) (72) → LinkGapGE: HDXConc.SecondEigLE on N_τ (HDXConc.linkVerts) with the zero-diagonal weights W_τij (HDXConc.linkWeight) and threshold 1 − λ_τ; reason: P_τ is the walk of these weights and is self-adjoint in L²(π_τ); Courant–Fischer
--   - encoding: max_{i∈N_τ} θ̄_τi; the levels T_int, T_bot, T_stop → ⨆ over the finite nonempty subtype N_τ; τ.card + 2 ≤ d, τ.card + 2 = d, τ.card + 1 = d; reason: N_τ is nonempty at internal faces, so the supremum is the maximum
--   - encoding: Gram norm θ_τ = ‖Σ π_τ(i) E_τ,i|_{I_τ}‖ → norm of the map I_τ → K obtained by composing with the inclusion; reason: the range lies in I_τ and the inclusion is isometric
--   - encoding: δ_τ defined recursively by (83) on T_int → an input function δ satisfying (83) as an equation on faces with τ.card + 2 ≤ d; reason: the recursion determines δ uniquely from the terminal bounds; same instances
--   - encoding: L_τ ⪰ 0 acting on I_τ; operator inequalities ⪰ → a continuous linear map I_τ → I_τ that is IsPositive (self-adjoint, nonnegative form); inequalities as quadratic forms; reason: standard meaning of ⪰ for self-adjoint operators
--   - encoding: each link graph with m_τ ≥ 2 is connected (p.30) → SteurerHDX.IsConnectedComplex X d: the 1-skeleton of SteurerHDX.link X τ, whose vertices are the singletons {x} with x ∈ N_τ and whose edges are the pairs with τ ∪ {x, y} ∈ X, is connected for every face with τ.card + 2 ≤ d; reason: this graph is isomorphic to the link graph on N_τ (x ↦ {x}); same instances
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), proof of Theorem 5.2, eq. (86), p.35 (PDF 35)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_SteurerHDX_IsConnectedComplex
import Definitions.Def_ROLDescent_LinkGapGE
import Definitions.Def_ROLDescent_IsSubspaceHierarchy
import Definitions.Def_ROLDescent_gramNorm
import Definitions.Def_ROLDescent_gramUpdate

namespace ROLDescent

open scoped InnerProductSpace

/-- **Eq. (86): the nodewise energy bound L_τ ⪰ δ_τ id at every visited node.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), proof of
Theorem 5.2, eq. (86), p.35 (PDF 35): "We now prove the stronger nodewise energy bound
E_τ^eff(b) ≥ δ_τ‖b‖² (b ∈ I_τ), L_τ ⪰ δ_τ id_{I_τ}, (86) at every visited node."

**Formalization Note** Under all hypotheses of Theorem 5.2. "L_τ ⪰ δ_τ id" is its quadratic-form
reading. Every visited node is every face with `τ.card + 1 ≤ d` (internal and stopping faces).
Internal faces T_int are the faces with `τ.card + 2 ≤ d`; the bottom level T_bot (68) is
`τ.card + 2 = d`; T_int \ T_bot (m_τ ≥ 3) is `τ.card + 3 ≤ d`; stopping faces T_stop (67) are
`τ.card + 1 = d`. The Gram bounds θ̄ (overlined on the page) are an input function `θbar`, free on
T_bot (78) and satisfying the recursion (79) as an equation above it; this determines θ̄ uniquely
from the bottom inputs. `gramNorm` is the Gram norm θ_τ (75). The link-walk gap bounds λ_τ ∈ (0, 2]
(p.30) satisfy (72) on T_int \ T_bot. The maximum over the children is a supremum over the
(nonempty, finite) link vertices. Energies: `L τ` acts on the subspace `I_τ` (a map `I_τ → I_τ`, positive in Mathlib's sense: self-adjoint
with nonnegative quadratic form), defined on every visited face (`τ.card + 1 ≤ d`); `E_τ(b) =
⟨b, L_τ b⟩`. The assembly inequality (81) uses `R_a b = Π_τi b ∈ I_τi` and the normalization in
which the assembly coefficients are `π_τ(i)` (p.33). The terminal bounds δ_σ > 0 (82) are given on
T_stop, and δ satisfies the recursion (83) as an equation on T_int, which determines it uniquely. -/
theorem eq_86 {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ)
    (hX : WeightedComplex X d w) (hconn : SteurerHDX.IsConnectedComplex X d)
    (I : Finset V → Submodule ℂ K) (hI : IsSubspaceHierarchy X d I)
    (L : (τ : Finset V) → (↥(I τ) →L[ℂ] ↥(I τ)))
    (hL : ∀ τ ∈ X, τ.card + 1 ≤ d → (L τ).IsPositive)
    (θbar lam δ : Finset V → ℝ)
    (h78 : ∀ τ ∈ X, τ.card + 2 = d →
      gramNorm X d w I τ ≤ θbar τ ∧ θbar τ < 1 ∧ 0 ≤ θbar τ)
    (h72 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      0 < lam τ ∧ lam τ ≤ 2 ∧ LinkGapGE X d w τ (lam τ))
    (h79 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      θbar τ = gramUpdate (lam τ) (⨆ i : HDXConc.linkVerts X τ, θbar (insert (i : V) τ)))
    (h80 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      (⨆ i : HDXConc.linkVerts X τ, θbar (insert (i : V) τ)) < lam τ / 2)
    (h81 : ∀ τ ∈ X, τ.card + 2 ≤ d → ∀ b : ↥(I τ),
      ∑ i : HDXConc.linkVerts X τ, outProb X d w τ i *
        RCLike.re ⟪((I (insert (i : V) τ)).orthogonalProjectionOnto (b : K) : K),
          (L (insert (i : V) τ) ((I (insert (i : V) τ)).orthogonalProjectionOnto (b : K)) : K)⟫_ℂ
      ≤ RCLike.re ⟪(b : K), (L τ b : K)⟫_ℂ)
    (h82 : ∀ σ ∈ X, σ.card + 1 = d →
      0 < δ σ ∧ ∀ b : ↥(I σ), δ σ * ‖(b : K)‖ ^ 2 ≤ RCLike.re ⟪(b : K), (L σ b : K)⟫_ℂ)
    (h83 : ∀ τ ∈ X, τ.card + 2 ≤ d →
      δ τ = (1 - θbar τ) * ⨅ i : HDXConc.linkVerts X τ, δ (insert (i : V) τ)) :
    ∀ τ ∈ X, τ.card + 1 ≤ d → ∀ b : ↥(I τ),
      δ τ * ‖(b : K)‖ ^ 2 ≤ RCLike.re ⟪(b : K), (L τ b : K)⟫_ℂ := by sorry

end ROLDescent

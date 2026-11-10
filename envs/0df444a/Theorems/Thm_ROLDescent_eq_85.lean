-- Prove2me | Theorems.Thm_ROLDescent_eq_85
-- name    : ROLDescent.eq_85
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:27.563197+00:00
-- url     : https://prove2.me/theorems/dbff0496-fa7b-44fb-877d-abea2f3b3be2
-- title:
--   Eq. (85) — norm retention $\sum_a\pi_\tau(i)\|R_ab\|^2\ge(1-\theta_\tau)\|b\|^2$, and $\theta_\tau<1$
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d$, $(\mathcal I_\tau)$ a subspace hierarchy, and $\tau$ an internal face. For every $b \in \mathcal I_\tau$,
--
--   $$\sum_{i \in N_\tau} \pi_\tau(i) \|\Pi_{\tau i} b\|^2 = \|b\|^2 - \sum_{i \in N_\tau} \pi_\tau(i) \|E_{\tau,i} b\|^2 \ge (1 - \theta_\tau) \|b\|^2,$$
--
--   where $R_a b = \Pi_{\tau i} b$ is the localization of $b$ along $a : \tau \to \tau i$ and $\theta_\tau$ is the Gram norm. Equivalently, $\sum_a \pi_\tau(i) R_a^* R_a = \mathrm{id} - \sum_i \pi_\tau(i) E_{\tau,i}|_{\mathcal I_\tau} \succeq (1 - \theta_\tau)\,\mathrm{id}$. Moreover
--
--   $$\theta_\tau < 1 .$$
--
--   Thus $1 - \theta_\tau$ is the fraction of squared norm guaranteed to survive one localization step on average.
--
--   Differences from the source:
--   - encoding: operator identity and inequality (85) on I_τ → the same identity and inequality as quadratic forms ⟨b, ·b⟩ for every b ∈ I_τ; reason: a self-adjoint operator on a complex space is determined by its quadratic form
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.5.1, eq. (85), pp.34–35 (PDF 34–35)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_IsSubspaceHierarchy
import Definitions.Def_ROLDescent_gramNorm

namespace ROLDescent

/-- **Eq. (85): norm retention, and θ_τ < 1.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.5.1, pp.34–35 (PDF 34–35):
"For b ∈ I_τ and a : τ → τi, localization retains R_a b and removes E_τ,i b. These components are
orthogonal, so ‖R_a b‖² = ‖b‖² − ‖E_τ,i b‖². Averaging over the outgoing branches and using
Σ_i π_τ(i) = 1 gives Σ_{a:τ→τi} π_τ(i)‖R_a b‖² = ‖b‖² − Σ_i π_τ(i)‖E_τ,i b‖² ≥ (1 − θ_τ)‖b‖². …
Equivalently, in operator form, Σ_{a:τ→τi} π_τ(i) R_a* R_a = id_{I_τ} − Σ_i π_τ(i) E_τ,i|_{I_τ}
⪰ (1 − θ_τ) id_{I_τ}. (85) The span condition and finite dimensionality imply θ_τ < 1".

**Formalization Note** At an internal face (τ.card + 2 ≤ d). `R_a b = Π_τi b`; the operator identity
and inequality (85) are stated in quadratic-form form for every `b ∈ I_τ` (over ℂ a self-adjoint
operator on `I_τ` is determined by its quadratic form). -/
theorem eq_85 {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (I : Finset V → Submodule ℂ K) (hI : IsSubspaceHierarchy X d I)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ b : ↥(I τ),
      ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i * ‖(I (insert i τ)).starProjection (b : K)‖ ^ 2 =
        ‖(b : K)‖ ^ 2 - ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i *
          ‖((I τ).starProjection - (I (insert i τ)).starProjection) (b : K)‖ ^ 2 ∧
      (1 - gramNorm X d w I τ) * ‖(b : K)‖ ^ 2 ≤
        ‖(b : K)‖ ^ 2 - ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i *
          ‖((I τ).starProjection - (I (insert i τ)).starProjection) (b : K)‖ ^ 2) ∧
    gramNorm X d w I τ < 1 := by sorry

end ROLDescent

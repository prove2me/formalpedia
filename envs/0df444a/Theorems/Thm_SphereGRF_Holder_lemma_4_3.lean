-- Prove2me | Theorems.Thm_SphereGRF_Holder_lemma_4_3
-- name    : SphereGRF.Holder.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:49.724502+00:00
-- url     : https://prove2.me/theorems/b70fdce8-e89b-4aac-926d-6a1fe539ba09
-- title:
--   Lemma 4.3 — even moments of field increments
-- statement:
--   Let $T$ be an isotropic Gaussian random field on $S^2$ with angular power spectrum $(A_\ell)$ satisfying $\sum_{\ell\ge0}A_\ell\ell^{1+\beta}<\infty$ for $0\le\beta\le2$. For each positive integer $p$, there is a constant $C_{\beta,p}$, independent of $x$ and $y$, such that
--
--   $$
--   \mathbb E|T(x)-T(y)|^{2p}\le C_{\beta,p}d(x,y)^{\beta p}\qquad(x,y\in S^2).
--   $$
--
--   These moment bounds are the probabilistic input to the modification theorem. **Formalization Note** The moment is an extended nonnegative integral, so a nonintegrable moment cannot evaluate to a spurious zero.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Lemma 4.3, p. 17

import Mathlib
import Definitions.Def_SphereGRF_Holder_Setting

open MeasureTheory ProbabilityTheory Polynomial
noncomputable section

namespace SphereGRF.Holder

theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : S2 → Ω → ℝ) (A : ℕ → ℝ) (β : ℝ)
    (hT : IsIsotropicGRF P T A) (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA : Summable (fun ℓ : ℕ => A ℓ * (ℓ : ℝ) ^ (1 + β))) :
    ∀ p : ℕ, 1 ≤ p → ∃ C : ℝ, ∀ x y : S2,
      ∫⁻ ω, ‖T x ω - T y ω‖ₑ ^ (2 * p) ∂P ≤
        ENNReal.ofReal (C * geoDist x y ^ (β * p)) := by sorry

end SphereGRF.Holder

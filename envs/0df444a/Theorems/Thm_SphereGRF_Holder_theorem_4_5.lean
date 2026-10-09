-- Prove2me | Theorems.Thm_SphereGRF_Holder_theorem_4_5
-- name    : SphereGRF.Holder.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:52.970982+00:00
-- url     : https://prove2.me/theorems/3784eda8-d7f1-4b90-b423-c1233899e56e
-- title:
--   Theorem 4.5 — spectral summability gives Hölder sample paths
-- statement:
--   Let $T$ be an isotropic Gaussian random field on $S^2$ with angular power spectrum $(A_\ell)$. Suppose $0<\beta\le2$ and
--
--   $$
--   \sum_{\ell=0}^{\infty}A_\ell\ell^{1+\beta}<\infty.
--   $$
--
--   Then there is one continuous modification of $T$ whose paths are Hölder continuous with every exponent $0<\gamma<\beta/2$, measured with the geodesic distance.
--
--   The theorem turns spectral summability into regularity of sample paths. **Formalization Note** The field may have a nonzero constant mean. The modification agrees with $T$ almost everywhere at each sphere point; exceptional paths are redefined, allowing the pathwise conclusion for every sample.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Theorem 4.5, p. 20

import Mathlib
import Definitions.Def_SphereGRF_Holder_Setting

open MeasureTheory ProbabilityTheory Polynomial
noncomputable section

namespace SphereGRF.Holder

theorem theorem_4_5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : S2 → Ω → ℝ) (A : ℕ → ℝ) (β : ℝ)
    (hT : IsIsotropicGRF P T A) (hβ : 0 < β) (hβ2 : β ≤ 2)
    (hA : Summable (fun ℓ : ℕ => A ℓ * (ℓ : ℝ) ^ (1 + β))) :
    ∃ T' : S2 → Ω → ℝ,
      (∀ x : S2, T' x =ᵐ[P] T x) ∧
      IsRandomField P T' ∧
      (∀ ω : Ω, Continuous (fun x : S2 => T' x ω)) ∧
      ∀ γ : ℝ, 0 < γ → γ < β / 2 → ∀ ω : Ω, ∃ K : ℝ,
        ∀ x y : S2, |T' x ω - T' y ω| ≤ K * geoDist x y ^ γ := by sorry

end SphereGRF.Holder

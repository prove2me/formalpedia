-- Prove2me | Theorems.Thm_SphereGRF_Truncation_proposition_5_2
-- name    : SphereGRF.Truncation.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:15.247434+00:00
-- url     : https://prove2.me/theorems/ec403da4-b482-4e7b-a9c8-4de59fe91367
-- title:
--   Proposition 5.2, p. 25 — explicit mean-square truncation rate
-- statement:
--   Let $T$ be the centered isotropic Gaussian field represented by the series in §5, and let $T^\kappa$ retain its degrees through $\kappa$. Suppose $A_\ell\ge0$, $C>0$, $\alpha>2$, and $\ell_0\ge1$, with $A_\ell\le C\ell^{-\alpha}$ whenever $\ell>\ell_0$. Then $T^\kappa\to T$ in $L^2(\Omega;L^2(S^2))$, and for every $\kappa\ge\ell_0$,
--
--   $$
--   \|T-T^\kappa\|_{L^2(\Omega;L^2(S^2))}
--     \le \widehat C\,\kappa^{-(\alpha-2)/2},\qquad
--   \widehat C^2=C\left(\frac{2}{\alpha-2}+\frac{1}{\alpha-1}\right).
--   $$
--
--   The estimate supplies the explicit constant and the $L^2$ rate used by the higher-moment bound.
--
--   **Formalization Note** The field is the specific KL-series representation defined on page 25; Lemma 5.1 identifies its law with that of an arbitrary centered isotropic field. The Gaussian input and nonnegative-spectrum assumptions spell out the representation's standing conditions. The norm is extended nonnegative, with the real bound embedded by `ENNReal.ofReal`.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Proposition 5.2, p. 25

import Mathlib
import Definitions.Def_SphereGRF_Truncation_Setting

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace SphereGRF.Truncation

theorem proposition_5_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → ℝ) (X : ℕ → ℕ → Fin 2 → Ω → ℝ)
    (C α : ℝ) (ℓ₀ : ℕ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ) (hC : 0 < C) (hα : 2 < α) (hℓ₀ : 1 ≤ ℓ₀)
    (hdec : ∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α))
    (hX : IsKLInput P X) :
    Tendsto (fun κ : ℕ => lpL2Norm P 2
      (fun ω y => klField A X ω y - klTrunc A X κ ω y)) atTop (𝓝 0) ∧
    ∀ κ : ℕ, ℓ₀ ≤ κ →
      lpL2Norm P 2 (fun ω y => klField A X ω y - klTrunc A X κ ω y) ≤
        ENNReal.ofReal (Real.sqrt (C * (2 / (α - 2) + 1 / (α - 1))) *
          (κ : ℝ) ^ (-(α - 2) / 2)) := by sorry

end SphereGRF.Truncation

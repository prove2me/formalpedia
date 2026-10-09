-- Prove2me | Theorems.Thm_SphereGRF_Truncation_theorem_5_3
-- name    : SphereGRF.Truncation.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:45.099994+00:00
-- url     : https://prove2.me/theorems/9fd4d711-2375-49e0-93b2-ac6ab712f742
-- title:
--   Theorem 5.3, p. 27 — mixed $L^p$ truncation rate for every finite $p\ge1$
-- statement:
--   Fix finite $p\ge1$, $C>0$, and $\alpha>2$. There is a positive constant $\widehat C_p$, depending only on these three parameters, such that every centered isotropic Gaussian KL field with nonnegative spectrum satisfying $A_\ell\le C\ell^{-\alpha}$ for $\ell>\ell_0\ge1$ has $T^\kappa\to T$ in $L^p(\Omega;L^2(S^2))$ and, for every $\kappa\ge\ell_0$,
--
--   $$
--   \|T-T^\kappa\|_{L^p(\Omega;L^2(S^2))}
--     \le \widehat C_p\,\kappa^{-(\alpha-2)/2}.
--   $$
--
--   The exponent is independent of $p$, which permits the almost-sure rate in Corollary 5.4.
--
--   **Formalization Note** The constant is quantified before the probability space, spectrum, Gaussian coefficients, and cutoff; it therefore cannot depend on those data. The explicit KL series is the representation of the paper's field, and the Gaussian input assumptions record the conditions in Lemma 5.1.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Theorem 5.3, p. 27

import Mathlib
import Definitions.Def_SphereGRF_Truncation_Setting

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace SphereGRF.Truncation

theorem theorem_5_3 :
    ∀ p C α : ℝ, 1 ≤ p → 0 < C → 2 < α →
      ∃ Cp : ℝ, 0 < Cp ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (A : ℕ → ℝ) (X : ℕ → ℕ → Fin 2 → Ω → ℝ) (ℓ₀ : ℕ),
        (∀ ℓ, 0 ≤ A ℓ) → 1 ≤ ℓ₀ →
        (∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α)) →
        IsKLInput P X →
        Tendsto (fun κ : ℕ => lpL2Norm P p
          (fun ω y => klField A X ω y - klTrunc A X κ ω y)) atTop (𝓝 0) ∧
        (∀ κ : ℕ, ℓ₀ ≤ κ →
          lpL2Norm P p (fun ω y => klField A X ω y - klTrunc A X κ ω y) ≤
            ENNReal.ofReal (Cp * (κ : ℝ) ^ (-(α - 2) / 2))) := by sorry

end SphereGRF.Truncation

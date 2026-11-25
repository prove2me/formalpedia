-- Prove2me | Theorems.Thm_PI_WMI_MMap_Fq_scale
-- name    : PI.WMI.MMap.Fq_scale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:17.968844+00:00
-- url     : https://prove2.me/theorems/c10b8dd4-92ad-5282-9d8c-7c407f7bcbc5
-- title:
--   MMap: Fq scale
-- statement:
--   The MMap construction uses the Fq scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L160-L169

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)

theorem PI.WMI.MMap.Fq_scale (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (θ : Fin N → ℝ) (x : V) :
    aeval (fun v : Fin N × Fin N => C (Complex.exp ((θ v.2 : ℂ) * Complex.I)) * X v) (Fq hP v0 x) =
      C (Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I)) * Fq hP v0 x := by sorry

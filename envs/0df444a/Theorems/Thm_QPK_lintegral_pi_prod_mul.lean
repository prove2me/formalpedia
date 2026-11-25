-- Prove2me | Theorems.Thm_QPK_lintegral_pi_prod_mul
-- name    : QPK.lintegral_pi_prod_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:55.871993+00:00
-- url     : https://prove2.me/theorems/abfb0e4c-ead6-44b5-9b24-3e25e6b3845e
-- title:
--   QPK: lintegral pi prod mul
-- statement:
--   The QPK construction uses the lintegral pi prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/WeilQuotientGlobalAssumptions.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/WeilQuotientGlobalAssumptions.lean#L43-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]

theorem QPK.lintegral_pi_prod_mul (μ ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] (φ : ∀ v, G v → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    ∫⁻ p, ∏ v, φ v (p.1 v * p.2 v) ∂((Measure.pi μ).prod (Measure.pi ν)) =
      ∏ v, ∫⁻ s, φ v s ∂(mulMap (μ v) (ν v)) := by sorry

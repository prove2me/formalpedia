-- Prove2me | Theorems.Thm_PI_GI_isCompact_mul_integer
-- name    : PI.GI.isCompact_mul_integer
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:34.247971+00:00
-- url     : https://prove2.me/theorems/5d5f8b47-22ae-40fd-9744-48e09417a904
-- title:
--   GI: is Compact mul integer
-- statement:
--   The GI construction uses the is Compact mul integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianDualMeasure/SecondCountableTopologyAndT2Space.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianDualMeasure/SecondCountableTopologyAndT2Space.lean#L43-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
noncomputable section
open PI PI.GI
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem PI.GI.isCompact_mul_integer (x : F) : IsCompact ((fun u => x * u) '' (𝒪[F] : Set F)) := by sorry

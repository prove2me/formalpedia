-- Prove2me | Theorems.Thm_PI_GreenHCLabel_supportExists_of
-- name    : PI.GreenHCLabel.supportExists_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:09.011876+00:00
-- url     : https://prove2.me/theorems/c5224c41-3509-4bde-b658-246c13031f76
-- title:
--   Green HCLabel: support Exists of
-- statement:
--   The Green HCLabel construction uses the support Exists of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/SupportExistsOf.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/SupportExistsOf.lean#L48-L54

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_GreenHCLabelOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
open PI PI.GreenHCLabel
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {K}

theorem PI.GreenHCLabel.supportExists_of (h1 : Jacquet K) (h2 : Frob K) (h3 : HCFin K) (h4 : ConstSymm) : SupportExists K := by sorry

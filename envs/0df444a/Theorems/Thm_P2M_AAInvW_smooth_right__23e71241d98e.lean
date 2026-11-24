-- Prove2me | Theorems.Thm_P2M_AAInvW_smooth_right__23e71241d98e
-- name    : P2M_AAInvW_smooth_right__23e71241d98e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:51:44.467484+00:00
-- url     : https://prove2.me/theorems/43a1bffc-20ac-4916-9e9f-0c44a45e1096
-- title:
--   P2 M AAInv W smooth right  23e71241d98e: P2 M AAInv W smooth right  23e71241d98e
-- statement:
--   The P2 M AAInv W smooth right  23e71241d98e construction uses the P2 M AAInv W smooth right  23e71241d98e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L54-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_AAInvW_smooth_right__23e71241d98e : SmoothRight := by sorry

alias «AAInvW».«smooth_right'» := P2M_AAInvW_smooth_right__23e71241d98e

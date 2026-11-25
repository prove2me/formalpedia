-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_isSymm_smul
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.isSymm_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:56.590935+00:00
-- url     : https://prove2.me/theorems/efa2a9e1-d4ff-5355-b4cf-0de39d5d1cba
-- title:
--   UG: is Symm smul
-- statement:
--   The UG construction uses the is Symm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L67-L71

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.isSymm_smul (hs : h.IsSymm) {u : K} (hus : star u = u) : (u⁻¹ • h).IsSymm := by sorry

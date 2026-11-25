-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_quasi
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_quasi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:57.852543+00:00
-- url     : https://prove2.me/theorems/2116512b-8a8b-5c03-8fcb-00076fb310be
-- title:
--   UG: exists quasi
-- statement:
--   The UG construction uses the exists quasi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L114-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L114-L142

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

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_quasi (hs : h.IsSymm) (w : V) {a : K} (ha : a + star a = a * star a * h w w) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, τ v = v - (a * h w v) • w := by sorry

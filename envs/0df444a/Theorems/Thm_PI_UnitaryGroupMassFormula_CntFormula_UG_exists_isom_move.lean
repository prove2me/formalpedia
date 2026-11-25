-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_isom_move
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_move
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:17.586935+00:00
-- url     : https://prove2.me/theorems/bfff2330-56bc-581c-af56-d9f2f8183a85
-- title:
--   UG: exists isom move
-- statement:
--   The UG construction uses the exists isom move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L144-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L144-L215

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

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_move (hS : IsHermSemilocal S) (hs : h.IsSymm) {x z : V} {u : K} (hu0 : u ≠ 0)
    (hus : star u = u) (hx : h x x = u) (hz : h z z = u) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = z ∧ ∀ v, h x v = 0 → h z v = 0 → τ v = v := by sorry

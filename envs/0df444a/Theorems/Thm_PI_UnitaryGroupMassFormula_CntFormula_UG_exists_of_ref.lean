-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_of_ref
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_of_ref
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:03.244785+00:00
-- url     : https://prove2.me/theorems/d1405a4d-8541-55da-bd35-f4dc4469d743
-- title:
--   UG: exists of ref
-- statement:
--   The UG construction uses the exists of ref property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L73-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L73-L112

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

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_of_ref (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {ι : Type}
    [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} {u : K} (hu : IsUnitIn S u) (hus : star u = u) (hrr : h r r = u)
    (hrx : ∀ i, h (x i) r = 0) :
    ∃ z ∈ M, h z z = u ∧ ∀ i, h (x i) z = 0 := by sorry

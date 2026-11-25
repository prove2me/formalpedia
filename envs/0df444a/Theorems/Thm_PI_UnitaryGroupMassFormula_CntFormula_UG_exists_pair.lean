-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_pair
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:07.550824+00:00
-- url     : https://prove2.me/theorems/9de0cb1e-fcbc-425a-83dd-ab51fb59e27a
-- title:
--   UG: exists pair
-- statement:
--   The UG construction uses the exists pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L20-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomMove.lean#L20-L65

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

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_pair (hS : IsHermSemilocal S) (hM : IsSelfDualMod S h M) {ι : Type} [Fintype ι]
    (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} (hr : ∃ v, h v r ≠ 0) (hrx : ∀ i, h (x i) r = 0) :
    ∃ α : K, α ≠ 0 ∧ α⁻¹ • r ∈ M ∧ ∃ w ∈ M, h w (α⁻¹ • r) = 1 ∧ ∀ i, h (x i) w = 0 := by sorry

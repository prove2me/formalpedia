-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_isom_frameU
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_frameU
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:11.366873+00:00
-- url     : https://prove2.me/theorems/fb3f89b7-ed97-55d3-818f-ee8d1faee6ca
-- title:
--   UG: exists isom frame U
-- statement:
--   The UG construction uses the exists isom frame U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomSelfDual.lean#L51-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomSelfDual.lean#L51-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_frameU (hS : IsHermSemilocal S) (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {n : ℕ} (x : Fin n → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (x i) ∈ M := by sorry

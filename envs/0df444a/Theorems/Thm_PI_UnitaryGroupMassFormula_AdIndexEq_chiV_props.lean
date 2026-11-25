-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_chiV_props
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.chiV_props
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:39.81288+00:00
-- url     : https://prove2.me/theorems/153d8318-f2f4-47fa-87b2-9a967e7cfa14
-- title:
--   Ad Index Eq: chi V props
-- statement:
--   The Ad Index Eq construction uses the chi V props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L94-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L94-L139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

theorem PI.UnitaryGroupMassFormula.AdIndexEq.chiV_props (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob) :
    (∀ g, 0 < chiV I v hC hL hJ g) ∧
    (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → chiV I v hC hL hJ s = 1) ∧
    (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧
        (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) →
        chiV I v hC hL hJ s = 1) := by sorry

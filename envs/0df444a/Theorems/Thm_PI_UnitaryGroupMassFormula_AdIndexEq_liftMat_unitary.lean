-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_liftMat_unitary
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.liftMat_unitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:38:51.769564+00:00
-- url     : https://prove2.me/theorems/134e7a05-de47-4d1e-9def-ab1c2e099a4f
-- title:
--   Ad Index Eq: lift Mat unitary
-- statement:
--   The Ad Index Eq construction uses the lift Mat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LiftMatMapSame.lean#L190-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LiftMatMapSame.lean#L190-L223

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
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
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.liftMat_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) (hg : g ∈ Uv I v) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (liftMat I v g.val) *
              I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * liftMat I v g.val =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by sorry

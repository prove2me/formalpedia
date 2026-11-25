-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_Gl_matV_listProd
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.Gl.matV_listProd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:04.144809+00:00
-- url     : https://prove2.me/theorems/c2a36c47-861f-415b-b67e-b96f5690f35b
-- title:
--   Gl: mat V list Prod
-- statement:
--   The Gl construction uses the mat V list Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L71-L87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
open Classical

theorem PI.UnitaryGroupMassFormula.ScXuExists.Gl.matV_listProd (I : AutInst) (loc : ∀ v, GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (Y : HeightOneSpectrum (𝓞 I.F) → I.Gf)
    (hY1 : ∀ v, matV I v (Y v : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = loc v)
    (hY2 : ∀ v, SuppAt I v (Y v)) (l : List (HeightOneSpectrum (𝓞 I.F))) (hl : l.Nodup)
    (w : HeightOneSpectrum (𝓞 I.F)) :
    matV I w (((l.map Y).prod : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      if w ∈ l then loc w else 1 := by sorry

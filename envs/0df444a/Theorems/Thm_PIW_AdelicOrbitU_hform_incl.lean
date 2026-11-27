-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_incl
-- name    : PIW.AdelicOrbitU.hform_incl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:44.399623+00:00
-- url     : https://prove2.me/theorems/4d05ed06-09f3-485b-9505-734747fa2f48
-- title:
--   Adelic Orbit U: hform incl
-- statement:
--   The Adelic Orbit U construction uses the hform incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L34-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem PIW.AdelicOrbitU.hform_incl (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (v i)) (fun i => inclR R (w i)) =
      inclR R (hE σ J v w) := by sorry

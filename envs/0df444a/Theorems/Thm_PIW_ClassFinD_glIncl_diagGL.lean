-- Prove2me | Theorems.Thm_PIW_ClassFinD_glIncl_diagGL
-- name    : PIW.ClassFinD.glIncl_diagGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:44.433004+00:00
-- url     : https://prove2.me/theorems/ef7a6316-3940-4ab1-b1ac-cc35169b3932
-- title:
--   Class Fin D: gl Incl diag GL
-- statement:
--   The Class Fin D construction uses the gl Incl diag GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L40-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain

theorem PIW.ClassFinD.glIncl_diagGL (F : Type) [Field F] [NumberField F] (n : ℕ) (f : Fin n → Fˣ) :
    glIncl F n (diagGL n f) =
      diagGL n (fun i => Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (f i)) := by sorry

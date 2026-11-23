-- Prove2me | Theorems.Thm_PIW_ClassFinD_Icf_v_mul
-- name    : PIW.ClassFinD.Icf.v_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:26.891705+00:00
-- url     : https://prove2.me/theorems/1b3383e4-200e-4429-ae11-0f5ce415966a
-- title:
--   Icf: v mul
-- statement:
--   The Icf construction uses the v mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L12-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PIW.ClassFinD.Icf.v_mul (x y : FiniteAdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((x * y) w) = Valued.v (x w) * Valued.v (y w) := by sorry

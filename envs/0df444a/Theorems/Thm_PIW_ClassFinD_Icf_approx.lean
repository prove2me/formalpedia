-- Prove2me | Theorems.Thm_PIW_ClassFinD_Icf_approx
-- name    : PIW.ClassFinD.Icf.approx
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:50.773046+00:00
-- url     : https://prove2.me/theorems/2d5e7578-b63d-4cb3-9385-af55a18642b5
-- title:
--   Icf: approx
-- statement:
--   The Icf construction uses the approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L67-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L67-L113

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

theorem PIW.ClassFinD.Icf.approx (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ∈ latI b ∧ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤ v.intValuation a := by sorry

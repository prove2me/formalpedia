-- Prove2me | Theorems.Thm_PIW_ClassFinD_Icf_mem_latI
-- name    : PIW.ClassFinD.Icf.mem_latI
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:29.264054+00:00
-- url     : https://prove2.me/theorems/e9fda542-4794-548b-b74c-5888a9d91a4e
-- title:
--   Icf: mem lat I
-- statement:
--   The Icf construction uses the mem lat I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L52-L54

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

theorem PIW.ClassFinD.Icf.mem_latI {b : (FiniteAdeleRing (𝓞 F) F)ˣ} {x : 𝓞 F} :
    x ∈ latI b ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) := by sorry

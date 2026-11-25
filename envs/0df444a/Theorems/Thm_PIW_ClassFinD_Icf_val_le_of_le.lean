-- Prove2me | Theorems.Thm_PIW_ClassFinD_Icf_val_le_of_le
-- name    : PIW.ClassFinD.Icf.val_le_of_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:50.159844+00:00
-- url     : https://prove2.me/theorems/82d0eaa0-8756-4336-9deb-dfc25b0e8e25
-- title:
--   Icf: val le of le
-- statement:
--   The Icf construction uses the val le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean#L115-L129

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

theorem PIW.ClassFinD.Icf.val_le_of_le (b b' : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    {x y : 𝓞 F} (h : Ideal.span {x} * latI b ≤ Ideal.span {y} * latI b') (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤
      v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by sorry

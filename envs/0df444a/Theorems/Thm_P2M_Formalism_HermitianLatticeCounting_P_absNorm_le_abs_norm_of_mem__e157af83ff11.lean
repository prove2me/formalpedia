-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11
-- name    : P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:34.301013+00:00
-- url     : https://prove2.me/theorems/1c3b02bf-20d6-455c-b33a-6140faccdff2
-- title:
--   P2 M Formalism Hermitian Lattice Counting P abs Norm le abs norm of mem  e157af83ff11: P2 M Formalism Hermitian Lattice Counting P abs Norm le abs norm of mem  e157af83ff11
-- statement:
--   The P2 M Formalism Hermitian Lattice Counting P abs Norm le abs norm of mem  e157af83ff11 construction uses the P2 M Formalism Hermitian Lattice Counting P abs Norm le abs norm of mem  e157af83ff11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L366-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L366-L392

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

theorem P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11 (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (x : E) (hx : x ∈ aa) (hx0 : x ≠ 0) :
    FractionalIdeal.absNorm aa ≤ |Algebra.norm ℚ x| := by sorry

alias «Formalism».«HermitianLatticeCounting».«P».«absNorm_le_abs_norm_of_mem'» := P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11

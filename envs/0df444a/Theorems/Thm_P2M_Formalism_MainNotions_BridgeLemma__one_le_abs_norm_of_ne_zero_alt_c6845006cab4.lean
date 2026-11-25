-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4
-- name    : P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:09.094941+00:00
-- url     : https://prove2.me/theorems/04fd0703-5246-4803-a59d-416a6b0151a5
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  one le abs norm of ne zero alt c6845006cab4: P2 M Formalism Main Notions Bridge Lemma  one le abs norm of ne zero alt c6845006cab4
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  one le abs norm of ne zero alt c6845006cab4 construction uses the P2 M Formalism Main Notions Bridge Lemma  one le abs norm of ne zero alt c6845006cab4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L23-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
variable (K : Type) [Field K] [NumberField K]

theorem P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4 (a : 𝓞 K) (ha : a ≠ 0) : (1 : ℝ) ≤ |((Algebra.norm ℚ (a : K) : ℚ) : ℝ)| := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«one_le_abs_norm_of_ne_zero_alt» := P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4

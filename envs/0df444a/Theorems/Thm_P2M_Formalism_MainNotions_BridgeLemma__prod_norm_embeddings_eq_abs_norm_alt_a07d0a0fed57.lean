-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57
-- name    : P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:46.916326+00:00
-- url     : https://prove2.me/theorems/a0e8de46-03cf-44d5-9fb4-2c00aaf65462
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  prod norm embeddings eq abs norm alt a07d0a0fed57: P2 M Formalism Main Notions Bridge Lemma  prod norm embeddings eq abs norm alt a07d0a0fed57
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  prod norm embeddings eq abs norm alt a07d0a0fed57 construction uses the P2 M Formalism Main Notions Bridge Lemma  prod norm embeddings eq abs norm alt a07d0a0fed57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L16-L21

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

theorem P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57 (a : K) : ∏ φ : K →+* ℂ, ‖φ a‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«prod_norm_embeddings_eq_abs_norm_alt» := P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57

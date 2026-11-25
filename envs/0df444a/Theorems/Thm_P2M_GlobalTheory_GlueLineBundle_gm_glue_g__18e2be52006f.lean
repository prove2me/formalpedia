-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f
-- name    : P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:04.044078+00:00
-- url     : https://prove2.me/theorems/569d45de-b08a-456e-82e9-ff081e46adb1
-- title:
--   P2 M Global Theory Glue Line Bundle gm glue g  18e2be52006f: P2 M Global Theory Glue Line Bundle gm glue g  18e2be52006f
-- statement:
--   The P2 M Global Theory Glue Line Bundle gm glue g  18e2be52006f construction uses the P2 M Global Theory Glue Line Bundle gm glue g  18e2be52006f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L100-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

theorem P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by sorry

alias «GlobalTheory».«GlueLineBundle».«gm_glue_g'» := P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f

-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isDominant_homOfVector_of_quasiFiniteAt__199183cd97e7
-- name    : P2M_GlobalTheory_T_isDominant_homOfVector_of_quasiFiniteAt__199183cd97e7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:09.156663+00:00
-- url     : https://prove2.me/theorems/8b97d122-3e34-4102-94f1-1d2161939d58
-- title:
--   P2 M Global Theory T is Dominant hom Of Vector of quasi Finite At  199183cd97e7: P2 M Global Theory T is Dominant hom Of Vector of quasi Finite At  199183cd97e7
-- statement:
--   The P2 M Global Theory T is Dominant hom Of Vector of quasi Finite At  199183cd97e7 construction uses the P2 M Global Theory T is Dominant hom Of Vector of quasi Finite At  199183cd97e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsDominantHomOfVectorOfQuasiFiniteAtStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsDominantHomOfVectorOfQuasiFiniteAtStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem P2M_GlobalTheory_T_isDominant_homOfVector_of_quasiFiniteAt__199183cd97e7 : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by sorry

alias «GlobalTheory».«T».«isDominant_homOfVector_of_quasiFiniteAt'» := P2M_GlobalTheory_T_isDominant_homOfVector_of_quasiFiniteAt__199183cd97e7

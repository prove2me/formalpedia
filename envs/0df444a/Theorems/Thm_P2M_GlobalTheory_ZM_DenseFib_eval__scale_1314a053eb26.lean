-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZM_DenseFib_eval__scale_1314a053eb26
-- name    : P2M_GlobalTheory_ZM_DenseFib_eval__scale_1314a053eb26
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:02:33.519663+00:00
-- url     : https://prove2.me/theorems/c1dfcc9d-0008-45a0-9f7b-c4b5b6ac6f9a
-- title:
--   P2 M Global Theory ZM Dense Fib eval  scale 1314a053eb26: P2 M Global Theory ZM Dense Fib eval  scale 1314a053eb26
-- statement:
--   The P2 M Global Theory ZM Dense Fib eval  scale 1314a053eb26 construction uses the P2 M Global Theory ZM Dense Fib eval  scale 1314a053eb26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L28-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemIdealOfOfDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DenseFib

theorem P2M_GlobalTheory_ZM_DenseFib_eval__scale_1314a053eb26 {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by sorry

alias «GlobalTheory».«ZM».«DenseFib».«eval₂_scale» := P2M_GlobalTheory_ZM_DenseFib_eval__scale_1314a053eb26

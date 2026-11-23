-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndivisibleSection_cst_one__21ea7f0379b8
-- name    : P2M_GlobalTheory_IndivisibleSection_cst_one__21ea7f0379b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:57.717744+00:00
-- url     : https://prove2.me/theorems/e95440a1-9326-4e84-8685-d8d77843f4a6
-- title:
--   P2 M Global Theory Indivisible Section cst one  21ea7f0379b8: P2 M Global Theory Indivisible Section cst one  21ea7f0379b8
-- statement:
--   The P2 M Global Theory Indivisible Section cst one  21ea7f0379b8 construction uses the P2 M Global Theory Indivisible Section cst one  21ea7f0379b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsGeneratorOfBasis.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsGeneratorOfBasis.lean#L28-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem P2M_GlobalTheory_IndivisibleSection_cst_one__21ea7f0379b8 (q : Z ⟶ Sp R) (z : Z) : cst q z 1 = 1 := by sorry

alias «GlobalTheory».«IndivisibleSection».«cst_one'» := P2M_GlobalTheory_IndivisibleSection_cst_one__21ea7f0379b8

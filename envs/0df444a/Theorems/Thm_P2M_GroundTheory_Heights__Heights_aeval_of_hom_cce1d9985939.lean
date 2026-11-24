-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939
-- name    : P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:02.908945+00:00
-- url     : https://prove2.me/theorems/512d1a7e-bb96-4ede-abc7-2b47f107c141
-- title:
--   P2 M Ground Theory Heights  Heights aeval of hom cce1d9985939: P2 M Ground Theory Heights  Heights aeval of hom cce1d9985939
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval of hom cce1d9985939 construction uses the P2 M Ground Theory Heights  Heights aeval of hom cce1d9985939 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L176-L180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939 {Ω : Type} [Field Ω] (φ : MvPolynomial (Coord n) ℤ →+* Ω)
    (f : MvPolynomial (Coord n) ℤ) : aeval (fun v ↦ φ (X v)) f = φ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_of_hom» := P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939

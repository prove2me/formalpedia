-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_mat_a5253d6a3533
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_mat_a5253d6a3533
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:47.404816+00:00
-- url     : https://prove2.me/theorems/92259fd1-c0be-4687-aa48-dc3860b978f0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous mat a5253d6a3533: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous mat a5253d6a3533
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous mat a5253d6a3533 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous mat a5253d6a3533 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLevi.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLevi.lean#L42-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_mat_a5253d6a3533 (w : InfinitePlace E) : Continuous fun g : archUnitary h v => mat g w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«continuous_mat» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_mat_a5253d6a3533

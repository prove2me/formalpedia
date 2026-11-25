-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:10.937817+00:00
-- url     : https://prove2.me/theorems/7db666be-02c2-427f-a4eb-41ebd772d449
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv Apply 3885da6a041b: P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv Apply 3885da6a041b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv Apply 3885da6a041b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv Apply 3885da6a041b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArithmeticCovolumeFinite.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArithmeticCovolumeFinite.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArithmeticCovolumeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«continuous_len_invApply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b

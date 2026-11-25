-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_vecAt_smul_b03500ff132f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_vecAt_smul_b03500ff132f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:46.48282+00:00
-- url     : https://prove2.me/theorems/50cd9c50-093c-4201-b71f-f65e454f5732
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul vec At smul b03500ff132f: P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul vec At smul b03500ff132f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul vec At smul b03500ff132f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul vec At smul b03500ff132f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L16-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedLenSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [NumberField E] [IsTotallyComplex E] [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_vecAt_smul_b03500ff132f (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightedLenSmul».«vecAt_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_vecAt_smul_b03500ff132f

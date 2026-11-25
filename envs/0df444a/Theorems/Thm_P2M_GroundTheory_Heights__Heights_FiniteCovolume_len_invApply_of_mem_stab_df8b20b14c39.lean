-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_len_invApply_of_mem_stab_df8b20b14c39
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_len_invApply_of_mem_stab_df8b20b14c39
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:43.804404+00:00
-- url     : https://prove2.me/theorems/00da3184-9509-504f-8d38-aade511f8a62
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume len inv Apply of mem stab df8b20b14c39: P2 M Ground Theory Heights  Heights Finite Covolume len inv Apply of mem stab df8b20b14c39
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume len inv Apply of mem stab df8b20b14c39 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume len inv Apply of mem stab df8b20b14c39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L36-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_len_invApply_of_mem_stab_df8b20b14c39 {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    {k : archUnitary h v} (hk : k ∈ M.stab) (y : InfinitePlace E → ι → ℂ) :
    M.len (invApply k y) = M.len y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«len_invApply_of_mem_stab» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_len_invApply_of_mem_stab_df8b20b14c39

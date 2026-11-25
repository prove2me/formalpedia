-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca
-- name    : P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:01.265992+00:00
-- url     : https://prove2.me/theorems/6f3cc32b-0262-412b-b8b3-20615b077fd1
-- title:
--   P2 M Ground Theory Heights  Heights KLines Std Index Det span to Add Subgroup eq closure 4928e3faf5ca: P2 M Ground Theory Heights  Heights KLines Std Index Det span to Add Subgroup eq closure 4928e3fa
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Std Index Det span to Add Subgroup eq closure 4928e3faf5ca construction uses the P2 M Ground Theory Heights  Heights KLines Std Index Det span to Add Subgroup eq closure 4928e3faf5ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesStdIndexDet.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesStdIndexDet.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdIndexDet
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
open NumberField Matrix
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesStdIndexDet

theorem P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca (K : Type) [Field K] [NumberField K] (k : ℕ)
    (f : (Fin k → K) →ₗ[K] (Fin k → K)) :
    (Submodule.span (𝓞 K) (Set.range fun j : Fin k => f (Pi.single j 1))).toAddSubgroup =
      AddSubgroup.closure (Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesStdIndexDet».«span_toAddSubgroup_eq_closure» := P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca

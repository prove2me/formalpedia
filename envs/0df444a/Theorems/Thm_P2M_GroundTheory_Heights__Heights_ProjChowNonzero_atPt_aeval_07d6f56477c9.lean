-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_aeval_07d6f56477c9
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_aeval_07d6f56477c9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:55.922841+00:00
-- url     : https://prove2.me/theorems/9bf7ea42-ec4c-42e5-8b48-7c4ac9e7f293
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt aeval 07d6f56477c9: P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt aeval 07d6f56477c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt aeval 07d6f56477c9 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt aeval 07d6f56477c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L149-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_aeval_07d6f56477c9 {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    atPt e (aeval (locPar A) f) =
      aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive := fun _ => AlgebraicClosure ℂ)
        (algebraMap ℂ _ (A 0 ij.2)) (fun i => -algebraMap ℂ _ (A i.succ ij.2)) ij.1) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«atPt_aeval» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_aeval_07d6f56477c9

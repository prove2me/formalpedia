-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:00.7558+00:00
-- url     : https://prove2.me/theorems/c294c24c-a4a5-4ff4-add1-662ced0ff8ba
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H cont Diff eval mv Polynomial f33a1329f8bf: P2 M Ground Theory Heights  Heights Zero Locus Dim H cont Diff eval mv Polynomial f33a1329f8bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H cont Diff eval mv Polynomial f33a1329f8bf construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H cont Diff eval mv Polynomial f33a1329f8bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L102-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf {ι : Type*} [Fintype ι] (q : MvPolynomial ι ℂ) :
    ContDiff ℂ 1 (fun y : ι → ℂ => MvPolynomial.eval y q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«contDiff_eval_mvPolynomial» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf

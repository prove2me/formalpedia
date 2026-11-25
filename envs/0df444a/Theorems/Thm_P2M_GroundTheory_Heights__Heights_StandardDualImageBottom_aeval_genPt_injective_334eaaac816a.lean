-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:46.085658+00:00
-- url     : https://prove2.me/theorems/e0da4e95-d4ae-5c80-982f-267a5046320a
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval gen Pt injective 334eaaac816a: P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval gen Pt injective 334eaaac816a
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval gen Pt injective 334eaaac816a construction uses the P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval gen Pt injective 334eaaac816a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L61-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a : Function.Injective (aeval (R := ℤ) (genPt K i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualImageBottom».«aeval_genPt_injective» := P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a

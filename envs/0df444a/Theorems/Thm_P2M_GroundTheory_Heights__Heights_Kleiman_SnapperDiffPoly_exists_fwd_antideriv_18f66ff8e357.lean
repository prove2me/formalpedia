-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:31.93872+00:00
-- url     : https://prove2.me/theorems/f7dce7a6-8b7e-4e5a-a3a4-d2b6ecd60d10
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly exists fwd antideriv 18f66ff8e357: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly exists fwd antideriv 18f66ff8e357
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly exists fwd antideriv 18f66ff8e357 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly exists fwd antideriv 18f66ff8e357 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L41-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357 {K : Type} [DecidableEq K] (D : ℕ) (k : K) (q : MvPolynomial K ℚ)
    (hq : q = 0 ∨ q.totalDegree < D) : ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ D ∧
      ∀ x : K → ℚ, eval (x + Pi.single k 1) P - eval x P = eval x q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«exists_fwd_antideriv» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357

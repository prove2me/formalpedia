-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_amplifiedCoreWork_isBigO
-- name    : ThreeSum.StageBounds.amplifiedCoreWork_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:18.695856+00:00
-- url     : https://prove2.me/theorems/3ca5571b-79a6-4877-b038-48a73c210d53
-- title:
--   Stage Bounds: amplified Core Work is Big O
-- statement:
--   The Stage Bounds construction uses the amplified Core Work is Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L259-L270
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L259-L270

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.StageBounds.amplifiedCoreWork_isBigO {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    (fun n : ℕ => (amplifiedCoreWork C W H n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ targetExponent) := by sorry

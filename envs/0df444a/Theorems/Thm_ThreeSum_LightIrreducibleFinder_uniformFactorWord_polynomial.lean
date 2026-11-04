-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_uniformFactorWord_polynomial
-- name    : ThreeSum.LightIrreducibleFinder.uniformFactorWord_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:34.871969+00:00
-- url     : https://prove2.me/theorems/b1686ab1-4377-4427-bb16-eb75449bda79
-- title:
--   Light Irreducible Finder: uniform Factor Word polynomial
-- statement:
--   The Light Irreducible Finder construction uses the uniform Factor Word polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L91-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L91-L115

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000

theorem ThreeSum.LightIrreducibleFinder.uniformFactorWord_polynomial (d p q : ℕ) (hsize : p^d=q) :
    uniformFactorWord d p q ≤ 1000000*(d+p+q+2)^4 := by sorry

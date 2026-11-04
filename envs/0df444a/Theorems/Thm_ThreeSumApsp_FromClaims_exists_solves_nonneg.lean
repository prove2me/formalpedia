-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_exists_solves_nonneg
-- name    : ThreeSumApsp.FromClaims.exists_solves_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:34.016733+00:00
-- url     : https://prove2.me/theorems/80944cca-73f0-444e-8da1-92a9e58402bf
-- title:
--   From Claims: exists solves nonneg
-- statement:
--   If the running time `T` is realized, and `T ≤ C X` and `X ≥ 1` on the instances in `dom'`, whose
--   numbers are bounded by the `κ`-th power of the size, then a program solves them in `O(X)` steps.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L51-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L51-L58

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.exists_solves_nonneg {prob : Problem} {size bound : prob.Inst → ℕ}
    {dom dom' : prob.Inst → Prop} {T X : prob.Inst → ℝ} (hR : RealizedWithin prob size bound dom T)
    (κ : ℕ) {C : ℝ} (hdom : ∀ x, dom' x → dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ)
    (hT : ∀ x, dom' x → T x ≤ C * X x) (hX : ∀ x, dom' x → 1 ≤ X x) :
    ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob P b dom' fun x => K * X x := by sorry

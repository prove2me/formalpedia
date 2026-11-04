-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_admissible_meets
-- name    : ThreeSum.TernaryPhysicalDigitSpan.admissible_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:12.028002+00:00
-- url     : https://prove2.me/theorems/45934c6d-b748-4bc6-a7d0-7e784e3eb9de
-- title:
--   Ternary Physical Digit Span: admissible meets
-- statement:
--   Executed membership testing of only the J physical digits returns the
--   logical digit-comap admissibility bit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L114-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L114-L139

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryPhysicalDigitSpan.admissible_meets {lim : Limits} {P : Program}
    {pMain pEq catalog n candidate depth : ℕ}
    (hmain : P[pMain]?=some (LightSpanCatalogTest.body pEq))
    (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : Fin (J+2) → ZMod p)
    (rows : List (Fin J → ZMod p))
    (H : TernaryStoredSpan.Represents f n (rows.map (reversal J)))
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space)
    (hrow : candidate+J≤lim.space)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word) (hpp : (p : ℤ)≤lim.word)
    (hf : ∀k<n, ∀i<J, f k i<p)
    (hread : ∀k<n, ∀i<J, μ (catalog+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀i<J, μ (candidate+i)=(LightStoredSpan.rowValues (physicalDigits row) i : ℤ))
    (hd : depth+1≤lim.depth) :
    Meets lim P pMain depth [catalog,n,J,candidate] μ (LightSpanCatalogTest.time J n)
      (fun r ν => (r=1 ↔ row∉forbidden rows) ∧ ν=μ) := by sorry

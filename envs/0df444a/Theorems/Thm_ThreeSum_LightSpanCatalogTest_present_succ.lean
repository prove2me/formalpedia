-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogTest_present_succ
-- name    : ThreeSum.LightSpanCatalogTest.present_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:13.961607+00:00
-- url     : https://prove2.me/theorems/06bdaf1c-3d53-480f-b07d-1c10a09131ba
-- title:
--   Light Span Catalog Test: present succ
-- statement:
--   The Light Span Catalog Test construction uses the present succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L81-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L81-L90

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem ThreeSum.LightSpanCatalogTest.present_succ (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) :
    Present f row J (n+1) ↔ Present f row J n ∨ ∀ i<J, f n i=row i := by sorry

-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPairMass_pairMass_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass.pairMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:56:42.797292+00:00
-- url     : https://prove2.me/theorems/7925b8cb-4e78-4746-9d27-e4a4c7895e20
-- title:
--   pairMass_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPairMass.lean#L41-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPairMass.lean#L41-L72

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass.pairMass_le (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (M n : ℕ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hl : I.nB≤n) (hc : I.nC≤n) :
    pairBound (setup (r := r) maps τ cap Q I)*2^(N m r)≤envelope maps cap M n := by sorry

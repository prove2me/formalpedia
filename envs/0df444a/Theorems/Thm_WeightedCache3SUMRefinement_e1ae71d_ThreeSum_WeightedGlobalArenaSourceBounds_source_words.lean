-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceBounds_source_words
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.source_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:26:12.096189+00:00
-- url     : https://prove2.me/theorems/ee8fa13a-4c99-4322-931d-67196f3dbe67
-- title:
--   source_words
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L109-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L109-L152

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.source_words (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (right : Bool) (n U : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (hbank : nb m r≤(4^fixedLength m)^r) :
    let S := source (r := r) maps cap I right
    let A := numbers maps τ cap M b K H drift scale n U r
    LightRadixKeys.word S.p0 S.U0 r≤A.sourceWord ∧
    LightRadixKeys.word S.p1 S.U1 r≤A.sourceWord ∧
    LightRadixKeys.word S.p2 S.U2 r≤A.sourceWord ∧
    LightSourceResidues.word S.M S.M S.U 0≤A.sourceWord ∧
    S.bank+2^(S.W+1)+16≤A.sourceWord ∧
    S.groups*S.bank+1≤A.sourceWord ∧ S.factor≤A.sourceWord ∧
    S.factor*(count S.xs p r (p^r) S.NL S.input*I.weightCap)≤A.sourceWord ∧
    (count S.xs p r (p^r) S.NL S.input+1)*I.weightCap≤A.sourceWord := by sorry

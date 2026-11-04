-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_source_words
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.source_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:01:20.880794+00:00
-- url     : https://prove2.me/theorems/c1239808-2bf3-4ae8-afce-fe7e0974cc8b
-- title:
--   Weighted Global Arena Source Bounds: source words
-- statement:
--   Every scalar source-host word requirement is bounded by the one
--   concrete source-word footprint.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L109-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L109-L152

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.source_words (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
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

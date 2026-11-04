-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCompactSupport_support
-- name    : ThreeSum.WeightedGlobalArenaCompactSupport.support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:31:30.649592+00:00
-- url     : https://prove2.me/theorems/36ed13fd-d2f5-46f6-aa18-68138e4fcf9c
-- title:
--   Weighted Global Arena Compact Support: support
-- statement:
--   The actual compact native moment groups have bounded support once the
--   literal full native paired potential is zero. All singleton and physical
--   record restrictions are discharged inside this theorem.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCompactSupport.lean#L25-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCompactSupport.lean#L25-L108

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Definitions.Def_Submission_ThreeSum_TernaryTaggedMinorSupport
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Theorems.Thm_ThreeSum_TernaryTaggedMinorSupport_support
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_support

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCompactSupport
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore LightOriginalSurvivors
open TernaryExtensionEncoding TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F r J K : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaCompactSupport.support (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (L R : ℕ→ℕ→ℤ) (B C : ℕ→ℤ)
    (H : (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (O : ℕ→Fin r→ZMod p)
    (keysB keysC : ℕ→ℕ) (a b : Fin (J+2))
    (hB : ∀ j<I.nB, I.leftInput j=(coefficientCode (H (fun t => (L j t.val : ZMod p))) : ℤ))
    (hC : ∀ j<I.nC, I.rightInput j=(coefficientCode (H (fun t => (R j t.val : ZMod p))) : ℤ))
    (hO : ∀ j<I.requesterCount, I.targets j=(coefficientCode (O j) : ℤ))
    (hkB : ∀ j<I.nB, keysB j=coefficientCode (H (fun t => (L j t.val : ZMod p))))
    (hkC : ∀ j<I.nC, keysC j=coefficientCode (H (fun t => (R j t.val : ZMod p))))
    (hLtag : ∀ j<I.nB, L j a.val=1 ∧ L j b.val=0)
    (hRtag : ∀ j<I.nC, R j a.val=0 ∧ R j b.val=1)
    (hraw : ∀ u<I.nB, ∀ v<I.nC, ∀ u'<I.nB, ∀ v'<I.nC,
      (fun t : Fin (J+2) => (L u t.val : ZMod p))+(fun t => (R v t.val : ZMod p))=
      (fun t : Fin (J+2) => (L u' t.val : ZMod p))+(fun t => (R v' t.val : ZMod p))→
        C v-B u=C v'-B u')
    (hzero : pairedPotential (setup (r := r) maps τ cap Q I) K J L R=0) :
    let fB := index keysB I.nB
    let fC := index keysC I.nC
    let I' := WeightedGlobalArenaPairRestriction.restrict I (indices keysB I.nB).length
      (indices keysC I.nC).length fB fC
    ∀ i<(setup (r := r) maps τ cap Q I').front.count,
      (TernaryPairedSupport.physicalSupport
        (mode (fun j => B (fB j)) (fun j => C (fC j)) (S := setup (r := r) maps τ cap Q I') (i := i))).card≤2*p^K := by sorry

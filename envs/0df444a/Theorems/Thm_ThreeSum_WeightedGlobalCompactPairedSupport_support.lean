-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_support
-- name    : ThreeSum.WeightedGlobalCompactPairedSupport.support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:09:15.541198+00:00
-- url     : https://prove2.me/theorems/5fb14959-777a-4145-b164-f91d6d8a5221
-- title:
--   Weighted Global Compact Paired Support: support
-- statement:
--   The positions in this theorem are the physical compact-source positions,
--   not zero-weight placeholders for deleted original records.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L41-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L41-L87

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalCompactPairedSupport.support {F W G : Type*} [Field F] [Fintype F]
    [AddCommGroup W] [Module F W] [Fintype W] [Fintype G] [DecidableEq W]
    {nB nC J K total : ℕ} (keysB keysC : ℕ → ℕ) (B C : ℕ → ℤ)
    (L : Fin nB → Fin J → ℤ) (R : Fin nC → Fin J → ℤ)
    (H : (Fin J → F) →ₗ[F] W) (P : G → Type*) [∀ g, Fintype (P g)]
    (left : ∀ g, P g → Fin (indices keysB nB).length)
    (right : ∀ g, P g → Fin (indices keysC nC).length)
    (root : G → W)
    (hhashB : ∀ a b : Fin nB,
      H (fun j => (L a j : F)) = H (fun j => (L b j : F)) → keysB a.val = keysB b.val)
    (hhashC : ∀ a b : Fin nC,
      H (fun j => (R a j : F)) = H (fun j => (R b j : F)) → keysC a.val = keysC b.val)
    (hroot : ∀ g a,
      H ((fun j => (L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩ j : F))+
         (fun j => (R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩ j : F))) = root g)
    (hraw : ∀ g a b,
      (fun j => (L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩ j : F))+
        (fun j => (R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩ j : F)) =
      (fun j => (L ⟨index keysB nB (left g b).val,index_lt (left g b).isLt⟩ j : F))+
        (fun j => (R ⟨index keysC nC (right g b).val,index_lt (right g b).isLt⟩ j : F)) →
      C (index keysC nC (right g a).val)-B (index keysB nB (left g a).val) =
      C (index keysC nC (right g b).val)-B (index keysB nB (left g b).val))
    (hpotential : (∑ g : G, ∑ e : Fin K → P g,
      rowWeight (tupleMatrix
        (fun a => L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩)
        (fun a => R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩) e)) ≤ total)
    (hzero : total = 0) :
    ∀ g, (TernaryPairedSupport.physicalSupport (fun a : P g =>
      C (index keysC nC (right g a).val)-B (index keysB nB (left g a).val))).card ≤
        2*Fintype.card F^K := by sorry

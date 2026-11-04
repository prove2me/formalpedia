-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensorScaled_scaled_total
-- name    : ThreeSum.TernaryPairedTensorScaled.scaled_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:29.500116+00:00
-- url     : https://prove2.me/theorems/8d90916d-f9b5-47ed-8125-e347e88512af
-- title:
--   Ternary Paired Tensor Scaled: scaled total
-- statement:
--   The Ternary Paired Tensor Scaled construction uses the scaled total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensorScaled.lean#L42-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensorScaled.lean#L42-L56

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators

theorem ThreeSum.TernaryPairedTensorScaled.scaled_total {H : ℕ} {P : Fin H→Type*} [∀ i, Fintype (P i)]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : ∀ i, P i→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ (i : Fin H) (a b c d : Fin Λ),
      μ (base+i.val*Λ^4+tensorIndex Λ a.val b.val c.val d.val)=s*tensor (L i) (R i) a b c d) :
    LightTernaryPairedPotentialBatch.total K base Λ μ H=s^K*
      ((∑ i : Fin H, ∑ e : Fin K→P i, TernaryPairedPotential.rowWeight
        (Sum.elim (fun j => L i (e j)) (fun j => R i (e j)))) : ℤ) := by sorry

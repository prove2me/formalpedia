-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensorScaled_scaled_potential
-- name    : ThreeSum.TernaryPairedTensorScaled.scaled_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:33.993133+00:00
-- url     : https://prove2.me/theorems/0ef24a89-2509-45be-a4dc-fd9fc8048f53
-- title:
--   Ternary Paired Tensor Scaled: scaled potential
-- statement:
--   The Ternary Paired Tensor Scaled construction uses the scaled potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensorScaled.lean#L9-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensorScaled.lean#L9-L40

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators

theorem ThreeSum.TernaryPairedTensorScaled.scaled_potential {P : Type*} [Fintype P]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : P→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ a b c d : Fin Λ,
      μ (base+tensorIndex Λ a.val b.val c.val d.val)=s*tensor L R a b c d) :
    prefixSum K base Λ μ (Λ^width K)=s^K*
      ((∑ e : Fin K→P, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R (e i)))) : ℤ) := by sorry

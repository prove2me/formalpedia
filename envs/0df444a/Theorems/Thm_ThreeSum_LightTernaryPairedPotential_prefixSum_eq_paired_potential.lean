-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_prefixSum_eq_paired_potential
-- name    : ThreeSum.LightTernaryPairedPotential.prefixSum_eq_paired_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:43.973571+00:00
-- url     : https://prove2.me/theorems/89cedd2a-1ba4-4d4c-b0e8-6001a77dac74
-- title:
--   Light Ternary Paired Potential: prefix Sum eq paired potential
-- statement:
--   The Light Ternary Paired Potential construction uses the prefix Sum eq paired potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L61-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L61-L88

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.prefixSum_eq_paired_potential {P₀ : Type*} [Fintype P₀]
    (m base Λ : ℕ) (μ : ℕ → ℤ) (L R' : P₀ → Fin Λ → ℤ)
    (hTensor : ∀ a b c d : Fin Λ, μ (base+tensorIndex Λ a.val b.val c.val d.val)=tensor L R' a b c d) :
    prefixSum m base Λ μ (Λ^width m) =
      ((∑ e : Fin m → P₀, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) := by sorry

-- Prove2me | Theorems.Thm_UpperTheory_Mu_numeric_bound
-- name    : UpperTheory.Mu.numeric_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:01.760173+00:00
-- url     : https://prove2.me/theorems/f6b5d1e6-0c43-47fe-8b79-2dcae0de1c18
-- title:
--   Mu: numeric bound
-- statement:
--   The Mu construction uses the numeric bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/MassNumeric.lean#L6-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/MassNumeric.lean#L6-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LamLowNumericalEnd
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_MassNumeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Mu

theorem UpperTheory.Mu.numeric_bound {ι : Type} [Fintype ι] {w : ℕ} (f n r : ℕ) (hcard : Fintype.card ι = f) (L' dmax mass dim idx nrm E dO dS : ℝ)
    (H dk J deg : ι → ℝ) (h8 : 8 ≤ n) (h2 : 2 * r ≤ n) (h1 : 1 ≤ r) (hf : 1 ≤ f) (hL : (5.5 : ℝ) ≤ L') (hn : Real.log n ≤ L')
    (hd0 : 0 ≤ dmax) (hd : Real.log (dmax + 2) ≤ 2 * L') (hw0 : 0 < w) (hw : w ≤ 8 * f ^ 2)
    (hm : 1 / ((w : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass) (hdim : 1 ≤ dim)
    (hidx : idx * nrm = dS⁻¹) (hE : Real.exp (-(r * (2 * f))) ≤ E) (hO : 0 < dO ∧ dO ≤ Real.exp (2 * (r * (2 * f))))
    (hS : 0 < dS ∧ dS ≤ Real.exp (2 * (r * (2 * f)))) (hH : ∀ ρ, 0 < H ρ) (hk : ∀ ρ, 1 ≤ dk ρ) (hJ : ∀ ρ, 0 < J ρ)
    (hdeg : ∀ ρ, 0 ≤ deg ρ ∧ deg ρ ≤ dmax)
    (hJb : ∀ ρ, Real.log (J ρ)⁻¹ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (deg ρ + 2))) :
    0 < (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E ∧
      ∑ ρ, Real.log (H ρ) - 8 * f * (n : ℝ) ^ 2 * L' ≤
        Real.log ((∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E) := by sorry

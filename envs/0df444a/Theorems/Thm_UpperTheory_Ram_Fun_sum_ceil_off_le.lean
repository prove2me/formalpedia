-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_sum_ceil_off_le
-- name    : UpperTheory.Ram.Fun.sum_ceil_off_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:15.690117+00:00
-- url     : https://prove2.me/theorems/ad29186f-e9ba-47c1-89be-4cc8131d885e
-- title:
--   Fun: sum ceil off le
-- statement:
--   The Fun construction uses the sum ceil off le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunDen.lean#L12-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunDen.lean#L12-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp n_vp c_vp a0 delta_vp)
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun

theorem UpperTheory.Ram.Fun.sum_ceil_off_le {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime)
    (ha : ∀ l ∈ S, a0 𝔣 l = 0) {N : ℕ} (hN : N ≠ 0) (hd : ∀ l : ℕ, l.Prime → (l : ℤ) ∣ discr E → l ∣ N) {A : ℝ}
    (h1 : Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ≤ A) (h2 : Real.log N ≤ A) :
    ∑ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l ≤ ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
      (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 1) * A := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_le_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_le_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:57.974699+00:00
-- url     : https://prove2.me/theorems/6d82224c-e086-418a-b3e8-66702fc3a0bc
-- title:
--   Semi Pt: mid le zero
-- statement:
--   The Semi Pt construction uses the mid le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegN.lean#L10-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegN.lean#L10-L118

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_le_zero (hN : IntegralIndexStatement) (hA : AbsDetStatement) {K : Type} [Field K]
    [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Gm : Submodule (𝓞 K) (Fin r → K)) (hGm : Gm.FG)
    (hsupp : ∀ x ∈ Gm, ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0)
    (hint : IsIntegralOn (midForm S m g hfix) Gm)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ a, 0 < δ σ a)
    (hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖)
    (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gm) (k : ℕ) (c : Fin k → Fin r → K)
    (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_adapted_semistable
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.adapted_semistable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:49.768642+00:00
-- url     : https://prove2.me/theorems/fb37702f-d6d8-4033-b1d4-1fb04d904367
-- title:
--   Semi Pt: adapted semistable
-- statement:
--   The Semi Pt construction uses the adapted semistable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegW.lean#L51-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegW.lean#L51-L145

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.adapted_semistable (hB : LatDegBasisStatement) (hN : IntegralIndexStatement)
    (hA : AbsDetStatement) (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K) (h2m : 2 * m ≤ r)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (hg0 : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (Lp : Submodule (𝓞 K) (Fin r → K)) (hLp : Lp.FG)
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp)
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    ∃ dd : Fin r → ℝ, (∀ i, 0 < dd i) ∧ ∀ B ≤ Lp, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet (adMet r m g dd)) B b ≤ 0 := by sorry

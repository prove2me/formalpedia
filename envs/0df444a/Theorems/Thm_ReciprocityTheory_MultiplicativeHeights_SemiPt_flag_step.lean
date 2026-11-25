-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_flag_step
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.flag_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:07.708563+00:00
-- url     : https://prove2.me/theorems/a1d479b0-4567-43f0-96d6-5547727f1906
-- title:
--   Semi Pt: flag step
-- statement:
--   The Semi Pt construction uses the flag step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegW.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegW.lean#L33-L49

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.flag_step (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hLp : Lp.FG) (e' e : ℕ)
    (hP : ∀ B ≤ Lp ⊓ cutSub K r e', ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0)
    (hG : ∀ C ≤ (Lp ⊓ cutSub K r e).map (projGe K r e'), ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0) :
    ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0 := by sorry

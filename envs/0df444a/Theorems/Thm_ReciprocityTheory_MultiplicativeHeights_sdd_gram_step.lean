-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_gram_step
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_gram_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:23.618577+00:00
-- url     : https://prove2.me/theorems/acb1540d-69a5-462f-b65e-3174d5476412
-- title:
--   Multiplicative Heights: sdd gram step
-- statement:
--   The Multiplicative Heights construction uses the sdd gram step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegD.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegD.lean#L17-L62

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by sorry

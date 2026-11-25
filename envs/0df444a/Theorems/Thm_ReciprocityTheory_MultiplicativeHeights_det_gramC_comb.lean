-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_gramC_comb
-- name    : ReciprocityTheory.MultiplicativeHeights.det_gramC_comb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:10.740828+00:00
-- url     : https://prove2.me/theorems/84e91701-ee01-48f3-a834-19b7a926043d
-- title:
--   Multiplicative Heights: det gram C comb
-- statement:
--   The Multiplicative Heights construction uses the det gram C comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L39-L48

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.det_gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    (gramC H σ (fun j => ∑ i, N i j • b i)).det =
      ((Complex.normSq (σ N.det) : ℝ) : ℂ) * (gramC H σ b).det := by sorry

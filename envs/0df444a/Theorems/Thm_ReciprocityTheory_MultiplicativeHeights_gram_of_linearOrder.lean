-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gram_of_linearOrder
-- name    : ReciprocityTheory.MultiplicativeHeights.gram_of_linearOrder
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:58.632642+00:00
-- url     : https://prove2.me/theorems/63b861f5-1bd2-4e35-873a-baf68396b6ab
-- title:
--   Multiplicative Heights: gram of linear Order
-- statement:
--   The Multiplicative Heights construction uses the gram of linear Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GramOfLinearOrder.lean#L21-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GramOfLinearOrder.lean#L21-L96

import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
import Definitions.Def_ReciprocityTheory_SemistableReduction_GramOfLinearOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.gram_of_linearOrder {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)) (hF : F ≠ 0) :
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exp_torus_mean_le_l2_of_lex
-- name    : ReciprocityTheory.MultiplicativeHeights.exp_torus_mean_le_l2_of_lex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:25.917638+00:00
-- url     : https://prove2.me/theorems/ef240d93-ff4c-459f-afb2-94f37b871fa8
-- title:
--   Multiplicative Heights: exp torus mean le l2 of lex
-- statement:
--   The Multiplicative Heights construction uses the exp torus mean le l2 of lex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L7-L45

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset

theorem ReciprocityTheory.MultiplicativeHeights.exp_torus_mean_le_l2_of_lex {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by sorry

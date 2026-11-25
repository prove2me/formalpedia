-- Prove2me | Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba
-- name    : P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:12.284078+00:00
-- url     : https://prove2.me/theorems/8f55e070-67cc-4533-9cbf-725d3a704a0b
-- title:
--   P2 M Formalism Branching Determinant Cap xn R  615355f130ba: P2 M Formalism Branching Determinant Cap xn R  615355f130ba
-- statement:
--   The P2 M Formalism Branching Determinant Cap xn R  615355f130ba construction uses the P2 M Formalism Branching Determinant Cap xn R  615355f130ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L675-L682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L675-L682

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba (μ : ℕ → ℕ) (p i : ℕ) (hi : p ≤ i) (m : ℕ) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) = ∏ j ∈ Finset.range m, xnT μ i j := by sorry

alias «Formalism».«BranchingDeterminantCap».«xn_R'» := P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba

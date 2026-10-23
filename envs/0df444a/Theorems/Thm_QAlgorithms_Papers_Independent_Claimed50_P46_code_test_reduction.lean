-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_code_test_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.code_test_reduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:29:21.69599+00:00
-- url     : https://prove2.me/theorems/d018cd4a-663e-433a-a872-024227d1e58e
-- title:
--   Section VIII: stochastic code/test reduction (93)–(95) and deterministic converse
-- statement:
--   Let $P_n$ be a general source on a finite or countable alphabet $X^n$, with no independence or stationarity assumption. A code has a finite nonempty message set and arbitrary stochastic encoder and decoder, each normalized on every input. Write $\gamma_n$ for its error probability, $q_n=1-\gamma_n$ for success, and $L(\Phi)=\limsup_n n^{-1}\log|\Phi_n|$ for its extended real rate. Infima below range over all such code sequences. The counting-measure testing model compares $\rho_n=P_n$ with $\sigma_n(x)=1$. Choose any allowed likelihood family. Write $t_n(a)=\rho_n[I-S_n(-a)]$ for the upper self-information tail with its matched boundary choice; its complement is the matched lower tail. Logarithms are natural and zero probability has infinite exponent.
--
--   Every code induces a test
--   $$
--   T_n(x)=\sum_yF_n(y\mid x)G_n(x\mid y),\qquad
--   \gamma_n=\alpha_n[T_n],\qquad \beta_n[T_n]\le|\Phi_n|.
--   $$
--   Conversely, for every finite nonempty acceptance set $A\subseteq X^n$, there exists a code whose acceptance function is exactly $1_A$ and
--   $$
--   \gamma_n=\alpha_n[1_A],\qquad|\Phi_n|=\beta_n[1_A]=|A|.
--   $$
--
--   This is the full stochastic-code reduction and deterministic-test converse.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 17, Section VIII: stochastic code/test reduction (93)–(95) and deterministic converse

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Section VIII, PDF pp.17–18, (93)–(95) and deterministic converse.
Printed: every deterministic test induces a code with message set its acceptance region.
Changed: require that region finite and nonempty.
Why: a code has finitely many messages and every source input needs a normalized
encoder row; rejected inputs can send a fixed accepted symbol. -/
theorem code_test_reduction (P : Source.{u}) (k : ℕ) :
    (∀ C : StochasticSourceCode (P.X k), ∃ T : SimpleHypothesisTest (sourceSystem P k),
      (∀ x, (T x).val = codeAcceptance C x) ∧
      sourceCodeError P k C = testingTypeI T ∧ testingTypeII T ≤ (C.size : ℝ≥0∞)) ∧
    (∀ A : Finset (P.X k), A.Nonempty → ∃ C : StochasticSourceCode (P.X k),
      C.size = A.card ∧
      (∀ x, codeAcceptance C x = if x ∈ A then 1 else 0) ∧
      sourceCodeError P k C = testingTypeI (finiteAcceptanceTest P k A) ∧
      (C.size : ℝ≥0∞) = testingTypeII (finiteAcceptanceTest P k A) ∧
      testingTypeII (finiteAcceptanceTest P k A) = (A.card : ℝ≥0∞)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end

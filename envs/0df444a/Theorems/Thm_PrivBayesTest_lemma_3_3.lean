-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_3_3
-- name    : PrivBayesTest.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:23.651205+00:00
-- url     : https://prove2.me/theorems/15a83fd0-c3a2-4eb2-9c52-fc2c40587311
-- title:
--   Lemma 3.3: an $\varepsilon$-DP test with $-\log P_e^{(n)}\ge(n-1)C_\varepsilon(P;Q)-\log n$
-- statement:
--   Let $\varepsilon>0$, let $P,Q$ be probability measures on $\mathcal X$ and $(\pi_0,\pi_1)$ a prior with $\pi_0,\pi_1>0$. For every $n>0$ there is an $\varepsilon$-DP test $T\circ M$ on $n$ samples with
--
--   $$
--   -\log P_e^{(n)}(T\circ M)\;\ge\;(n-1)\,C_\varepsilon(P;Q)-\log n .
--   $$
--
--   This is the achievability half of Theorem 3.1; in the paper the test thresholds the Laplace statistic $\sum_i\bar\ell(X_i)+Z$ at $0$.
--
--   Differences from the source:
--   - encoding: test T ∘ M with M ε-DP and T : Y → {“P”, “Q”} → ε-DP Markov kernel from Xⁿ to Bool (true = “P”); reason: every T ∘ M is such a kernel (post-processing) and every such kernel is T ∘ M with T the identity; same class
--   - reading: prior π → π₀ > 0, π₁ > 0, π₀ + π₁ = 1; reason: the paper's standing assumption on the prior (p.1, 'a prior distribution π0, π1 > 0'); with π₀ = 0 the statement is false
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 3.3, p.16

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivBayesTest_bayesRisk
import Definitions.Def_PrivBayesTest_privChernoff

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- **Lemma 3.3** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.16. For all `n > 0` and any prior `π` there exist an ε-DP mechanism `M` and a
post-processing `T : Y → {"P", "Q"}` with `−log P_e^{(n)}(T ∘ M) ≥ (n − 1) C_ε(P; Q) − log n`.

**Formalization Note** The test `T ∘ M` is an ε-DP Markov kernel `κ : Xⁿ → Bool` (`true` = "`P`"); every
`T ∘ M` is one and conversely. The prior satisfies `π₀, π₁ > 0` (p.1) and `π₀ + π₁ = 1`. Values in
`EReal`; `C_ε` is `privChernoff`. -/
theorem lemma_3_3 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (π₀ π₁ : ℝ) (hπ₀ : 0 < π₀) (hπ₁ : 0 < π₁) (hπ : π₀ + π₁ = 1) (n : ℕ)
    (hn : 0 < n) :
    ∃ κ : Kernel (Fin n → X) Bool, IsMarkovKernel κ ∧ PrivLearn.Generic.IsDP (fun z => κ z) ε ∧
      ((((n : ℝ) - 1 : ℝ) : EReal) * privChernoff ε P Q - ((Real.log n : ℝ) : EReal)) ≤
        -ENNReal.log (bayesRisk P Q π₀ π₁ κ) := by sorry

end PrivBayesTest

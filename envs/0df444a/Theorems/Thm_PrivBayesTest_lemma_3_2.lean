-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_3_2
-- name    : PrivBayesTest.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:25.251836+00:00
-- url     : https://prove2.me/theorems/f402e976-6d00-4179-85c1-a5324fcd7955
-- title:
--   Lemma 3.2: $\limsup_n-\frac1n\log P_e^{(n)}(T\circ M)\le C_\varepsilon(P;Q)$ for every $\varepsilon$-DP test
-- statement:
--   Let $\varepsilon>0$, let $P,Q$ be probability measures on $\mathcal X$ and $(\pi_0,\pi_1)$ a prior with $\pi_0,\pi_1>0$. For every $\varepsilon$-DP mechanism $M$ on finite sequences of data points and every post-processing $T$ to $\{\text{"}P\text{"},\text{"}Q\text{"}\}$,
--
--   $$
--   \limsup_{n\to\infty}\ -\frac1n\log P_e^{(n)}(T\circ M)\;\le\;C_\varepsilon(P;Q).
--   $$
--
--   Equivalently: for every sequence $(T_n)$ of $\varepsilon$-DP tests, $T_n$ acting on $n$ samples, the exponent of the Bayes risk is asymptotically at most the private Chernoff information. This is the converse half of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: an ε-DP mechanism M : X* → Y with a post-processing T → a sequence (κₙ) of ε-DP Markov kernels κₙ : Xⁿ → Bool; reason: every (M, T) restricted to inputs of length n gives such a sequence, and every sequence arises from M(x) = κ_{|x|}(x) with T the identity
--   - reading: prior π → π₀ > 0, π₁ > 0, π₀ + π₁ = 1; reason: the paper's standing assumption on the prior (p.1, 'a prior distribution π0, π1 > 0'); with π₀ = 0 the statement is false
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 3.2, p.14

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivBayesTest_bayesRisk
import Definitions.Def_PrivBayesTest_privChernoff

open MeasureTheory ProbabilityTheory Filter

namespace PrivBayesTest

/-- **Lemma 3.2** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.14. For any prior `π`, ε-DP mechanism `M : X* → Y` and post-processing
`T : Y → {"P", "Q"}`, `lim sup_{n→∞} −(1/n) log P_e^{(n)}(T ∘ M) ≤ C_ε(P; Q)`.

**Formalization Note** The tests `T ∘ M` restricted to inputs of length `n` are an arbitrary sequence
`(κₙ)` of ε-DP Markov kernels `κₙ : Xⁿ → Bool` (`true` = "`P`"): every pair `(M, T)` gives one, and every
sequence arises from one. The prior satisfies the paper's standing assumption `π₀, π₁ > 0` (p.1) and
`π₀ + π₁ = 1`. Values in `EReal`; `C_ε` is `privChernoff`. -/
theorem lemma_3_2 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (π₀ π₁ : ℝ) (hπ₀ : 0 < π₀) (hπ₁ : 0 < π₁) (hπ : π₀ + π₁ = 1)
    (κ : ∀ n : ℕ, Kernel (Fin n → X) Bool) (hκm : ∀ n, IsMarkovKernel (κ n))
    (hκ : ∀ n, PrivLearn.Generic.IsDP (fun z => κ n z) ε) :
    limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * -ENNReal.log (bayesRisk P Q π₀ π₁ (κ n))) atTop ≤
      privChernoff ε P Q := by sorry

end PrivBayesTest

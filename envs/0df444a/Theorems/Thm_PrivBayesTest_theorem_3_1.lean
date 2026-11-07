-- Prove2me | Theorems.Thm_PrivBayesTest_theorem_3_1
-- name    : PrivBayesTest.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:52.713718+00:00
-- url     : https://prove2.me/theorems/55c06c65-7f85-45be-bc11-40a2909c55e2
-- title:
--   Theorem 3.1: the optimal $\varepsilon$-DP Bayes-risk exponent equals $C_\varepsilon(P;Q)$
-- statement:
--   Let $\varepsilon>0$, let $P,Q$ be probability measures on an arbitrary measurable space $\mathcal X$, and let $(\pi_0,\pi_1)$ be a prior with $\pi_0,\pi_1>0$. For a test $M$ on $n$ samples let $P_e^{(n)}(M)=\pi_0\Pr_{P^n}[M=\text{"}Q\text{"}]+\pi_1\Pr_{Q^n}[M=\text{"}P\text{"}]$ be its Bayes risk. Then the sequence of Definition 1.2 converges to the private Chernoff information $C_\varepsilon(P;Q)$, and
--
--   $$
--   \lim_{n\to\infty}\ \sup_{M\ \varepsilon\text{-DP}}\ -\frac1n\log P_e^{(n)}(M)\;=\;C_\varepsilon(P;Q),
--   $$
--
--   the supremum over all $\varepsilon$-differentially private tests on $n$ samples.
--
--   This is the paper's main result: the private Chernoff information is exactly the optimal error exponent of Bayesian hypothesis testing under $\varepsilon$-differential privacy, for every pair of distributions.
--
--   Differences from the source:
--   - generalization: lim_n sup_M −(1/n) log P_e^(n)(M) = C_ε(P; Q) → additionally: the Definition 1.2 sequence converges to C_ε(P; Q) (privChernoff); reason: makes explicit the limit that Definition 1.2 ('C_ε := lim') presupposes, so that privChernoff is not a junk limUnder value; §2.4 proves it
--   - encoding: test T ∘ M with M ε-DP and T : Y → {“P”, “Q”} → ε-DP Markov kernel from Xⁿ to Bool (true = “P”); reason: every T ∘ M is such a kernel (post-processing) and every such kernel is T ∘ M with T the identity; same class
--   - reading: prior π → π₀ > 0, π₁ > 0, π₀ + π₁ = 1; reason: the paper's standing assumption on the prior (p.1, 'a prior distribution π0, π1 > 0'); with π₀ = 0 the statement is false
--   - encoding: sup over ε-DP mechanisms in Definition 1.2 → sup over output spaces Y : Type with any σ-algebra and ε-DP Markov kernels to Y; reason: contains every output space the paper uses
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 3.1, p.13

import Mathlib
import Definitions.Def_PrivBayesTest_errExp
import Definitions.Def_PrivBayesTest_privChernoff

open MeasureTheory Filter Topology

namespace PrivBayesTest

/-- **Theorem 3.1** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.13. Let `ε > 0`. For any pair of distributions `P, Q` over `X` with prior
`π`, `lim_{n→∞} sup_{M ε-DP} −(1/n) log P_e^{(n)}(M) = C_ε(P; Q)`.

**Formalization Note** `X` is an arbitrary measurable space and `P, Q` arbitrary probability measures on
it. The prior satisfies the paper's standing assumption `π₀, π₁ > 0` (p.1, "a prior distribution
`π₀, π₁ > 0`") and `π₀ + π₁ = 1`; without positivity the statement is false. The supremum ranges over all
ε-DP tests: Markov kernels `κ : Xⁿ → Bool` (`true` = "`P`") satisfying `PrivLearn.Generic.IsDP`
(`errExp`). `C_ε` is `privChernoff`, the `limUnder` of the sequence of Definition 1.2; the first
conjunct states that this sequence converges (what "`C_ε := lim`" presupposes), so that `privChernoff`
is its true limit. Values in `EReal`. -/
theorem theorem_3_1 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (π₀ π₁ : ℝ) (hπ₀ : 0 < π₀) (hπ₁ : 0 < π₁) (hπ : π₀ + π₁ = 1) :
    Tendsto (chernoffSeq ε P Q) atTop (𝓝 (privChernoff ε P Q)) ∧
      Tendsto (errExp ε P Q π₀ π₁) atTop (𝓝 (privChernoff ε P Q)) := by sorry

end PrivBayesTest

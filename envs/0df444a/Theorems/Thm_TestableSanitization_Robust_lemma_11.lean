-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_11
-- name    : TestableSanitization.Robust.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:51:50.676174+00:00
-- url     : https://prove2.me/theorems/7290f73a-ad79-4cfc-91a5-90d008e991a5
-- title:
--   Lemma 11 — standard concentration bounds: Hoeffding, multiplicative Chernoff tails (also for means $\ge p$ / $\le p$), Markov
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space. Let $V_1,\dots,V_n$ ($n\ge1$) be independent random variables with values in $[0,1]$ and $\bar V=n^{-1}\sum_iV_i$.
--   1. **Hoeffding.** For $t>0$, $\Pr[|\bar V-\mathbb E\bar V|>t]\le2\exp(-2nt^2)$.
--   2. **Chernoff.** If the $V_i$ are Bernoulli with common mean $p$, then for $0<t\le1$
--   $$\Pr[\bar V\le(1-t)p]\le e^{-npt^2/2},\qquad \Pr[\bar V\ge(1+t)p]\le e^{-npt^2/(2+t)}.$$
--   3. For independent Bernoulli variables, the lower-tail bound also holds when every mean is at least $p$,
--   4. and the upper-tail bound when every mean is at most $p$ (here $p\in[0,1]$, $0<t\le1$).
--   5. **Markov.** For any nonnegative random variable $Y$ and $a>0$, $\Pr[Y>a]\le\mathbb EY/a$.
--
--   These are the concentration tools used in the analysis of the isolation test (Algorithm 3): Chernoff bounds for the per-point estimates $\tilde\phi_i$ and for the fraction of isolated sampled points, and Markov's inequality for the noise sensitivity and the norm of $x$.
--
--   Differences from the source:
--   - encoding: independent random variables V_1, …, V_n in [0, 1] (Bernoulli for the Chernoff clauses); a nonnegative random variable Y → measurable V : Fin n → Ω → ℝ on a probability space (Ω, P), mutually independent (iIndepFun), almost surely in [0, 1] (almost surely 0 or 1 for the Bernoulli clauses); Y measurable and pointwise nonnegative; reason: random variables are measurable functions; almost-sure value constraints are the usual meaning
--   - encoding: V_1, …, V_n (n a count of variables) → 0 < n; reason: the paper's list has at least one variable
--   - encoding: the extension sentence 'these bounds also hold when every mean is at least p for the lower tail, or at most p for the upper tail', with its coupling justification → two separate conjuncts (means ≥ p ⇒ lower tail; means ≤ p ⇒ upper tail) for p ∈ [0, 1] and 0 < t ≤ 1; the coupling remark (a proof) is not stated; reason: p is a Bernoulli mean in the coupling, so it lies in [0, 1]; the coupling explains why the clauses hold
--   - encoding: E V̄ as an expectation; E Y as an expectation → E V̄ as a Bochner integral (V̄ is bounded and measurable, hence integrable); E Y as the lower Lebesgue integral of ofReal ∘ Y in [0, ∞], divided by ofReal a; reason: for Y the lower integral is E Y when finite and +∞ otherwise, where the bound is trivial; no integrability side condition is added
--   - encoding: probabilities and expectations as real numbers → measures of sets and lower Lebesgue integrals in [0, ∞] (ENNReal), compared with ENNReal.ofReal of the real bounds; reason: the values lie in [0, 1]; ENNReal avoids integrability side conditions, and the measure of a possibly non-measurable set is its outer measure, which can only make an upper bound stronger
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 25 (PDF 27), Lemma 11

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TestableSanitization.Robust

theorem lemma_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (∀ (n : ℕ) (V : Fin n → Ω → ℝ), 0 < n → (∀ i, Measurable (V i)) → iIndepFun V P →
      (∀ i, ∀ᵐ ω ∂P, 0 ≤ V i ω ∧ V i ω ≤ 1) →
      ∀ t : ℝ, 0 < t →
        P {ω | t < |(∑ i, V i ω) / n - ∫ ω', (∑ i, V i ω') / n ∂P|} ≤
          ENNReal.ofReal (2 * Real.exp (-2 * n * t ^ 2))) ∧
    (∀ (n : ℕ) (V : Fin n → Ω → ℝ) (p : ℝ), 0 < n → (∀ i, Measurable (V i)) → iIndepFun V P →
      (∀ i, ∀ᵐ ω ∂P, V i ω = 0 ∨ V i ω = 1) → (∀ i, ∫ ω, V i ω ∂P = p) →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        P {ω | (∑ i, V i ω) / n ≤ (1 - t) * p} ≤ ENNReal.ofReal (Real.exp (-(n * p * t ^ 2 / 2))) ∧
        P {ω | (1 + t) * p ≤ (∑ i, V i ω) / n} ≤
          ENNReal.ofReal (Real.exp (-(n * p * t ^ 2 / (2 + t))))) ∧
    (∀ (n : ℕ) (V : Fin n → Ω → ℝ) (p : ℝ), 0 < n → 0 ≤ p → p ≤ 1 → (∀ i, Measurable (V i)) →
      iIndepFun V P → (∀ i, ∀ᵐ ω ∂P, V i ω = 0 ∨ V i ω = 1) → (∀ i, p ≤ ∫ ω, V i ω ∂P) →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        P {ω | (∑ i, V i ω) / n ≤ (1 - t) * p} ≤ ENNReal.ofReal (Real.exp (-(n * p * t ^ 2 / 2)))) ∧
    (∀ (n : ℕ) (V : Fin n → Ω → ℝ) (p : ℝ), 0 < n → 0 ≤ p → p ≤ 1 → (∀ i, Measurable (V i)) →
      iIndepFun V P → (∀ i, ∀ᵐ ω ∂P, V i ω = 0 ∨ V i ω = 1) → (∀ i, ∫ ω, V i ω ∂P ≤ p) →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        P {ω | (1 + t) * p ≤ (∑ i, V i ω) / n} ≤
          ENNReal.ofReal (Real.exp (-(n * p * t ^ 2 / (2 + t))))) ∧
    (∀ (Y : Ω → ℝ) (a : ℝ), Measurable Y → (∀ ω, 0 ≤ Y ω) → 0 < a →
      P {ω | a < Y ω} ≤ (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) / ENNReal.ofReal a) := by sorry

end TestableSanitization.Robust

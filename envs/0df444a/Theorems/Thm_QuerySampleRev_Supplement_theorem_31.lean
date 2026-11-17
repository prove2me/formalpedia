-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_31
-- name    : QuerySampleRev.Supplement.theorem_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:26:57.522675+00:00
-- url     : https://prove2.me/theorems/ecf2094f-d9f1-4c88-94a2-14294e188163
-- title:
--   Theorem 31 — multiplicative-accuracy DKW: $\mathbb P[\sup_{x\in[q,1]}|\hat F(x)/x-1|>\varepsilon']\le2e^{-nq\varepsilon'^2/(2(1+\varepsilon'/3))}$
-- statement:
--   **Theorem 31 (A multiplicative-accuracy DKW inequality).** Let $U_1,\dots,U_n$ be independent uniform random variables on $(0,1)$ and let
--   $$
--   \hat F(x)=\frac1n\sum_{i=1}^n\mathbb 1[U_i\le x],\qquad x\in[0,1],
--   $$
--   be their empirical distribution function.
--
--   1. For every $q\in(0,1)$, $\varepsilon'\in(0,1)$ and $n\ge1$,
--   $$
--   \mathbb P\Big[\sup_{x\in[q,1]}\Big|\frac{\hat F(x)}{x}-1\Big|>\varepsilon'\Big]\ \le\ 2\exp\Big(-\frac{nq\varepsilon'^2}{2(1+\varepsilon'/3)}\Big).
--   $$
--   2. Consequently, for every $\delta\in(0,1)$, if $n\ge\frac{2(1+\varepsilon'/3)}{q\varepsilon'^2}\log\frac2\delta$ then
--   $$
--   \mathbb P\big[(1-\varepsilon')x\le\hat F(x)\le(1+\varepsilon')x\ \text{ for every }x\in[q,1]\big]\ \ge\ 1-\delta .
--   $$
--   3. In particular, there is an absolute constant $C>0$ such that $n\ge C\,q^{-1}\varepsilon'^{-2}\log(1/\delta)$ suffices for the conclusion of 2, for all $q,\varepsilon'\in(0,1)$ and $0<\delta\le1/2$.
--
--   Unlike the classical (additive) DKW inequality, the error is relative to $x$, uniformly above the quantile threshold $q$; the paper uses it to estimate revenues from samples with relative accuracy.
--
--   **Formalization Note** The sample is distributed as the $n$-fold product of Lebesgue measure restricted to $(0,1)$, and $\hat F$ is the published empirical distribution function `MassartDKW.Tight.ecdf` (right-continuous: $\mathbb 1[U_i\le x]$). The supremum event is written as "some $x\in[q,1]$ has $|\hat F(x)/x-1|>\varepsilon'$".
--
--   Differences from the source:
--   - encoding: independent $U_1,\dots,U_n\sim\mathrm{Unif}(0,1)$ → the $n$-fold product of Lebesgue measure restricted to $(0,1)$ on $\mathbb R^{n}$, with the coordinate samples; reason: the canonical joint law of independent uniforms; every probability in the statement depends only on that law
--   - encoding: $\sup_{x\in[q,1]}|\hat F(x)/x-1|>\varepsilon'$ → $\exists x\in[q,1]$, $|\hat F(x)/x-1|>\varepsilon'$; reason: the supremum of a bounded set exceeds a number iff some element does
--   - reading: 'the sufficient sample size is $O(q^{-1}(\varepsilon')^{-2}\log(1/\delta))$ for $0<\delta\le1/2$' → $\exists$ absolute $C>0$: $n\ge Cq^{-1}\varepsilon'^{-2}\log(1/\delta)$ implies the conclusion of clause 2 for all $q,\varepsilon'\in(0,1)$, $\delta\in(0,1/2]$; reason: the standard reading of the asymptotic sample size, uniform in $q,\varepsilon',\delta$
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Appendix A, Theorem 31, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_MassartDKW_Tight_EmpiricalProcess

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 31 (A Multiplicative-Accuracy DKW Inequality).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Appendix A, Theorem 31, p.45
(PDF 47): "We consider independent uniform samples `U₁, …, Uₙ ∼ Unif(0, 1)`, with empirical distribution
function `F̂(x) ∶= (1/n) ∑_{i∈[n]} 1[Uᵢ ≤ x]` for all `x ∈ [0, 1]`. For every quantile threshold `q ∈ (0, 1)`,
relative-error tolerance `ε′ ∈ (0, 1)`, and sample size `n ≥ 1`, we have
`P[sup_{x∈[q,1]} |F̂(x)/x − 1| > ε′] ≤ 2 exp(−nq(ε′)²/(2(1 + ε′/3)))`. Consequently, for every failure
probability `δ ∈ (0, 1)`, a sample size satisfying `n ≥ (2(1+ε′/3)/(q(ε′)²)) log(2/δ)` ensures that
`P[(1 − ε′)x ≤ F̂(x) ≤ (1 + ε′)x for every x ∈ [q, 1]] ≥ 1 − δ`. In particular, the sufficient sample size is
`O(q^{−1}(ε′)^{−2} log(1/δ))` for `0 < δ ≤ 1/2`."

The sample `U = (U₀, …, U_{n−1})` is distributed as the product of `n` copies of the uniform law on `(0, 1)`
(Lebesgue measure restricted to `(0, 1)`), and `F̂` is the published empirical distribution function
`MassartDKW.Tight.ecdf` of the coordinates (right-continuous convention: `1[Uᵢ ≤ x]`, App. A, footnote 5).
Three clauses: (1) the tail bound; (2) the sample-size consequence; (3) one absolute `C > 0` such that
`n ≥ C q⁻¹ (ε′)⁻² log(1/δ)` suffices for the conclusion of (2), for every `q, ε′ ∈ (0, 1)`, `δ ∈ (0, 1/2]`.

**Formalization Note.** "`sup_{x∈[q,1]} |F̂(x)/x − 1| > ε′`" is written as "some `x ∈ [q, 1]` has
`|F̂(x)/x − 1| > ε′`" (the supremum of a bounded set exceeds `ε′` iff some element does). Probabilities are
measures of sets of samples. -/
theorem theorem_31 :
    (∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 < q → q < 1 → ∀ ε' : ℝ, 0 < ε' → ε' < 1 →
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioo 0 1))
          {U : Fin n → ℝ | ∃ x ∈ Set.Icc q 1,
            ε' < |MassartDKW.Tight.ecdf (fun i (V : Fin n → ℝ) => V i) U x / x - 1|} ≤
        ENNReal.ofReal (2 * Real.exp (-(n * q * ε' ^ 2 / (2 * (1 + ε' / 3)))))) ∧
    (∀ q : ℝ, 0 < q → q < 1 → ∀ ε' : ℝ, 0 < ε' → ε' < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ n : ℕ, 2 * (1 + ε' / 3) / (q * ε' ^ 2) * Real.log (2 / δ) ≤ n →
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioo 0 1))
            {U : Fin n → ℝ | ∀ x ∈ Set.Icc q 1,
              (1 - ε') * x ≤ MassartDKW.Tight.ecdf (fun i (V : Fin n → ℝ) => V i) U x ∧
              MassartDKW.Tight.ecdf (fun i (V : Fin n → ℝ) => V i) U x ≤ (1 + ε') * x}) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∀ ε' : ℝ, 0 < ε' → ε' < 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        ∀ n : ℕ, C * q⁻¹ * (ε' ^ 2)⁻¹ * Real.log (1 / δ) ≤ n →
          ENNReal.ofReal (1 - δ) ≤
            (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioo 0 1))
              {U : Fin n → ℝ | ∀ x ∈ Set.Icc q 1,
                (1 - ε') * x ≤ MassartDKW.Tight.ecdf (fun i (V : Fin n → ℝ) => V i) U x ∧
                MassartDKW.Tight.ecdf (fun i (V : Fin n → ℝ) => V i) U x ≤ (1 + ε') * x}) := by sorry

end QuerySampleRev.Supplement

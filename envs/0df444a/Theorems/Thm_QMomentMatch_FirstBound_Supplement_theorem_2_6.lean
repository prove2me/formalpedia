-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_theorem_2_6
-- name    : QMomentMatch.FirstBound.Supplement.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:15.764414+00:00
-- url     : https://prove2.me/theorems/5d90d9be-1c71-4562-83c7-f0a57226b7f9
-- title:
--   Theorem 2.6 — second moment-matching bound: $|\Pr_{\Pi_{0,N}}-\Pr_{\Pi_{1,N}}|\le C^A\frac{T^{2-2^{1-r}}}{N^{1-2^{1-r}}}+Ne^{-cN/A^2}$, and $o(1)$ for $T=o(N^{1/2-1/(2(2^r-1))})$
-- statement:
--   Let $A\ge1$ be an integer and $X_0,X_1$ positive frequency statistics supported on $[A]$, and let $\Pi_{0,N},\Pi_{1,N}$ be the distributions on functions $f:[N]\to[N]$ induced by $X_0,X_1$ through Definition 2.1. Suppose that for an integer $r\ge2$
--   $$\frac{\mathbb E[X_1]}{\mathbb E[X_0]}=\frac{\mathbb E[X_1^2]}{\mathbb E[X_0^2]}=\cdots=\frac{\mathbb E[X_1^{r-1}]}{\mathbb E[X_0^{r-1}]}.$$
--
--   1. There are absolute constants $c,C>0$ such that for all integers $N\ge CA$ and $0\le T\le c\sqrt N$, every $T$-query quantum algorithm $\mathcal A$ satisfies
--   $$\Big|\Pr_{f\sim\Pi_{0,N}}[\mathcal A^f=1]-\Pr_{f\sim\Pi_{1,N}}[\mathcal A^f=1]\Big|\le C^A\,\frac{T^{2-2^{1-r}}}{N^{1-2^{1-r}}}+N\exp\Big(-\frac{cN}{A^2}\Big).\qquad(9)$$
--   2. In particular, for fixed $A$ and $r$ (and fixed $X_0,X_1$), the difference is $o(1)$ as $N\to\infty$ whenever $T=o\big(N^{1/2-1/(2(2^r-1))}\big)$.
--
--   Each probability includes the draw of $f$ and the algorithm's measurement outcomes. For fixed $A,r$ this gives a stronger quantum query lower bound than Theorem 2.5, at the cost of the factor $C^A$; it is the paper's second main theorem and yields its applications for fixed support.
--
--   **Formalization Note** The constants $c,C$ are chosen before $A$, $X_0$, $X_1$, $r$, $N$, $T$ and the algorithm. The exponents are real: $T^{2-2^{1-r}}$ and $N^{1-2^{1-r}}$ use `Real.rpow`. Part 2 is stated for every sequence of algorithms indexed by $n$, with $N=n+1$, $T_n$ queries and workspace $\mathrm{Fin}(w_n)$: if $T_n/N^{1/2-1/(2(2^r-1))}\to0$ then the difference tends to $0$.
--
--   Differences from the source:
--   - reading: positive frequency statistics X_b supported on [A] → IsPosFreqStat: probability vectors on {0,…,A} with no mass at 0; reason: only the laws enter Definition 2.1 (base convention)
--   - encoding: a T-query quantum algorithm on f : [N] → [N] → QueryAlg (Fin N) (ZMod N) W T with any finite workspace W, any unitaries and start state, any output map out, standard oracle xorOracle f; reason: the base mission's algorithm model (theorem_2_5); [N] is Fin N for positions and ZMod N for labels
--   - encoding: o(1) as N → ∞ whenever T = o(N^{1/2−1/(2(2^r−1))}) → for all sequences T n, w n, alg n, out n with N = n + 1: Tendsto (T n / N^{1/2−1/(2(2^r−1))}) atTop (𝓝 0) → Tendsto |difference| atTop (𝓝 0); reason: the sequential definition of little-o; a workspace Fin (w n) is any finite workspace up to relabelling
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Theorem 2.6, p. 14 (proof §4, pp. 24–33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

namespace QMomentMatch.FirstBound.Supplement

open QAlgorithms QMomentMatch.FirstBound Filter Topology

/-- Theorem 2.6, p. 14 (proof §4, pp. 24–33): inequality (9) with absolute constants `c, C > 0`
(chosen before every other quantity), and the "In particular" clause for fixed `A, r`
(and fixed `X₀, X₁`), read over sequences of algorithms with `N = n + 1 → ∞`. -/
theorem theorem_2_6 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A : ℕ), 1 ≤ A → ∀ (X₀ X₁ : Fin (A + 1) → ℝ), IsPosFreqStat X₀ → IsPosFreqStat X₁ →
      ∀ (r : ℕ), 2 ≤ r → PropMoments X₀ X₁ r →
      ∀ (N T : ℕ) [NeZero N], C * A ≤ N → (T : ℝ) ≤ c * Real.sqrt N →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg (Fin N) (ZMod N) W T)
        (out : (Fin N × ZMod N) × W → Bool),
        |probAccept (inducedDist X₀ N) alg out - probAccept (inducedDist X₁ N) alg out| ≤
          C ^ A * ((T : ℝ) ^ ((2 : ℝ) - (2 : ℝ) ^ ((1 : ℝ) - r)) /
            (N : ℝ) ^ ((1 : ℝ) - (2 : ℝ) ^ ((1 : ℝ) - r))) +
          N * Real.exp (-(c * N / A ^ 2))) ∧
    (∀ (A : ℕ), 1 ≤ A → ∀ (X₀ X₁ : Fin (A + 1) → ℝ), IsPosFreqStat X₀ → IsPosFreqStat X₁ →
      ∀ (r : ℕ), 2 ≤ r → PropMoments X₀ X₁ r →
      ∀ (T w : ℕ → ℕ) (alg : ∀ n, QueryAlg (Fin (n + 1)) (ZMod (n + 1)) (Fin (w n)) (T n))
        (out : ∀ n, (Fin (n + 1) × ZMod (n + 1)) × Fin (w n) → Bool),
        Tendsto (fun n => (T n : ℝ) /
            ((n : ℝ) + 1) ^ ((1 : ℝ) / 2 - 1 / (2 * ((2 : ℝ) ^ r - 1)))) atTop (𝓝 0) →
        Tendsto (fun n => |probAccept (inducedDist X₀ (n + 1)) (alg n) (out n) -
            probAccept (inducedDist X₁ (n + 1)) (alg n) (out n)|) atTop (𝓝 0)) := by sorry

end QMomentMatch.FirstBound.Supplement

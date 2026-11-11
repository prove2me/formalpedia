-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_theorem_2_5
-- name    : QMomentMatch.FirstBound.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:00:59.387873+00:00
-- url     : https://prove2.me/theorems/4b877543-b740-4322-8282-7c075bf594a7
-- title:
--   Theorem 2.5 — matching $r-1$ moments: $|\Pr_{\Pi_{0,N}}-\Pr_{\Pi_{1,N}}|\le\frac NA\left(\frac{CAT^2}{r^2N}\right)^r+Ne^{-cN/A^2}$, and $o(1)$ for $T=o(N^{1/2-1/(2r)})$
-- statement:
--   Let $A\ge1$ be an integer and $X_0,X_1$ positive frequency statistics supported on $[A]$, and let $\Pi_{0,N},\Pi_{1,N}$ be the input distributions on functions $f:[N]\to[N]$ induced by $X_0,X_1$ through Definition 2.1. Suppose that for an integer $r\ge2$
--   $$\frac{\mathbb E[X_1]}{\mathbb E[X_0]}=\frac{\mathbb E[X_1^2]}{\mathbb E[X_0^2]}=\cdots=\frac{\mathbb E[X_1^{r-1}]}{\mathbb E[X_0^{r-1}]}.\tag{7}$$
--   There are absolute constants $c,C>0$ such that, for all integers $N\ge CA$ and $0\le T\le c\sqrt N$, every $T$-query quantum algorithm $\mathcal A$ (standard queries, any finite workspace) satisfies
--   $$\Big|\Pr_{f\sim\Pi_{0,N}}[\mathcal A^f=1]-\Pr_{f\sim\Pi_{1,N}}[\mathcal A^f=1]\Big|\le\frac NA\left(\frac{CAT^2}{r^2N}\right)^r+N\exp\!\left(-\frac{cN}{A^2}\right).\tag{8}$$
--   The constants $c,C$ are chosen before $A$, $X_0$, $X_1$, $r$, $N$, $T$ and the algorithm. Each probability includes the draw of $f$ and the algorithm's measurement.
--
--   In particular, if $A=O(r^2)$ and $A=o(\sqrt{N/\log N})$, the difference is $o(1)$ whenever $T=o(N^{1/2-1/(2r)})$ as $N\to\infty$. Here $A$, $r$, $X_0$, $X_1$, $T$ and the algorithm may all depend on $N$: for every $K$ and all sequences such that, for all large $N$, $A_N\ge1$, $r_N\ge2$, $X_0^{(N)},X_1^{(N)}$ satisfy (7) with $r_N$, and $A_N\le Kr_N^2$, and such that $A_N\sqrt{\log N/N}\to0$ and $T_N/N^{1/2-1/(2r_N)}\to0$, the difference of acceptance probabilities tends to $0$.
--
--   The bound shows that a quantum algorithm cannot distinguish two input distributions whose multiplicity statistics have proportional moments up to order $r-1$ with $o(N^{1/2-1/(2r)})$ queries; with $r$ growing this approaches the $\sqrt N$ barrier.
--
--   **Formalization Note** The proof (p. 23) gives $C=64e^2$ and $c=1/8$; the statement only asserts existence. Algorithms are `QAlgorithms.QueryAlg (Fin N) (ZMod N) W T`, with an arbitrary start state, arbitrary unitaries $U_0,\dots,U_T$, any finite workspace `W : Type`, and any Boolean map `out` of the final computational-basis outcome. In the asymptotic clause the sequences are indexed by $n$ with $N=n+1$, and the workspaces are `Fin (w n)`.
--
--   Differences from the source:
--   - reading: "positive frequency statistics $X_b$ supported on $[A]$" → any probability vectors on $\{1,\dots,A\}$; reason: only the laws enter Definition 2.1.
--   - encoding: "$T$-query" (at most $T$ queries) → `QueryAlg … T` (exactly $T$ oracle calls); reason: an algorithm with $T'\le T$ queries is covered by the statement for $T'$, and the right side of (8) is increasing in $T$.
--   - encoding: $f:[N]\to[N]$ with oracle $|i,y\rangle\mapsto|i,y+f(i)\bmod N\rangle$ → `f : Fin N → ZMod N` with `xorOracle f`; reason: 0-based domain and labels $j\mapsto j\bmod N$; the oracle is literally the same unitary.
--   - encoding: any finite workspace and final measurement → `W : Type` with `[Fintype W]`, computational-basis measurement and a Boolean map; reason: every finite workspace is equivalent to one in `Type`, and a general two-outcome measurement folds into $U_T$.
--   - encoding: integers $N\ge CA$ → `N : ℕ` with an instance `[NeZero N]`; reason: $N\ge CA\ge C>0$ already forces $N\ge1$.
--   - reading: "In particular, if $A=O(r^2)$ and $A=o(\sqrt{N/\log N})$, … $o(1)$ whenever $T=o(N^{1/2-1/(2r)})$" → a limit statement over sequences $A_N,r_N,X^{(N)}_b,T_N$, algorithms and workspaces indexed by $N=n+1$, with hypotheses holding eventually, $A_N\le Kr_N^2$, $A_N\sqrt{\log N/N}\to0$ and $T_N/N^{1/2-1/(2r_N)}\to0$; reason: the theorem's preamble fixes $A,r$, which would make the $o(\cdot)$ hypotheses on $A$ vacuous; the source's own use (Corollary 5.5, $r=\lceil\log N\rceil$) needs $N$-dependent parameters, and this stronger reading follows from (8).
--   - encoding: arbitrary finite workspaces in the asymptotic clause → workspaces Fin (w n); reason: every finite workspace is equivalent to Fin of its cardinality; transport of states, unitaries and output maps preserves acceptance probabilities.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Theorem 2.5, p. 14 (proof: §3.3, pp. 21–23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

namespace QMomentMatch.FirstBound

open QAlgorithms Filter Topology

/-- Theorem 2.5, p. 14: inequality (8) with absolute constants `c, C > 0`, and the
"In particular" clause, read over parameter sequences (`N = n + 1`). -/
theorem theorem_2_5 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A : ℕ), 1 ≤ A → ∀ (X₀ X₁ : Fin (A + 1) → ℝ), IsPosFreqStat X₀ → IsPosFreqStat X₁ →
      ∀ (r : ℕ), 2 ≤ r → PropMoments X₀ X₁ r →
      ∀ (N T : ℕ) [NeZero N], C * A ≤ N → (T : ℝ) ≤ c * Real.sqrt N →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg (Fin N) (ZMod N) W T)
        (out : (Fin N × ZMod N) × W → Bool),
        |probAccept (inducedDist X₀ N) alg out - probAccept (inducedDist X₁ N) alg out| ≤
          (N / A) * (C * A * T ^ 2 / (r ^ 2 * N)) ^ r + N * Real.exp (-(c * N / A ^ 2))) ∧
    (∀ (K : ℝ) (A r T w : ℕ → ℕ) (X₀ X₁ : ∀ n, Fin (A n + 1) → ℝ)
      (alg : ∀ n, QueryAlg (Fin (n + 1)) (ZMod (n + 1)) (Fin (w n)) (T n))
      (out : ∀ n, (Fin (n + 1) × ZMod (n + 1)) × Fin (w n) → Bool),
      (∀ᶠ n in atTop, 1 ≤ A n ∧ 2 ≤ r n ∧ IsPosFreqStat (X₀ n) ∧ IsPosFreqStat (X₁ n) ∧
        PropMoments (X₀ n) (X₁ n) (r n)) →
      (∀ᶠ n in atTop, (A n : ℝ) ≤ K * (r n : ℝ) ^ 2) →
      Tendsto (fun n => (A n : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)))
        atTop (𝓝 0) →
      Tendsto (fun n => (T n : ℝ) / ((n : ℝ) + 1) ^ ((1 : ℝ) / 2 - 1 / (2 * (r n : ℝ))))
        atTop (𝓝 0) →
      Tendsto (fun n => |probAccept (inducedDist (X₀ n) (n + 1)) (alg n) (out n) -
          probAccept (inducedDist (X₁ n) (n + 1)) (alg n) (out n)|) atTop (𝓝 0)) := by sorry

end QMomentMatch.FirstBound

-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_theorem_2_3
-- name    : SelectedSubset3SUM.Integer.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:38.382862+00:00
-- url     : https://prove2.me/theorems/34028586-3972-4d33-a49e-767881299b25
-- title:
--   Theorem 2.3 — full conditional unbalanced integer 3SUM reduction
-- statement:
--   Suppose a uniform deterministic real ring-arithmetic program solves every instance of Problem 2.1 in total time $O(P(n,d,t)+|\mathcal C|Q(n,d,t))$, for nonnegative cost functions $P,Q$. Fix any input-magnitude exponent $\kappa$. There is one finite randomized word-RAM program, with constants independent of its integer instances and of $t$, for the following task.
--
--   Given arbitrary finite $A,B,C\subseteq[N^\kappa]$, put $N=|A|+|B|$ and $\widehat n=\sqrt{|A||B|}$. For every natural $0\le t<\lg\widehat n$, let $d=\lceil t+\lg\widehat n+\lg\lg N+1\rceil$. The program answers $c\in A+B$ for every $c\in C$, with probability of any incorrect output $O(1/N)$ and worst-case total time
--
--   $$\widetilde O\!\left(\frac{\widehat n^2}{\binom d{2t}}(P(N,d,t)+N)+N\frac{\widehat n}{2^t}+|C|\frac{\widehat n}{2^t}(Q(N,d,t)+1)\right).$$
--
--   The tilde denotes a uniform power of $1+\lg N$. All integer input handling, original-integer correctness, subroutine simulation, random sampling, truncation, repetitions and output bits are included. No assumption is made about successful hashing or bounded simulation cost; those belong to the proof. The real-weight solver premise is retained without a coefficient restriction.
--
--   This reduction keeps the two input sizes and the query count separate and supplies the precise tradeoff used by Corollary 2.4.
--
--   Differences from the source:
--   - reading: solvability of Problem 2.1 in preprocessing-plus-query arithmetic time → one uniform finite ring-arithmetic solver for every real-weight instance, with nonnegative P,Q and bounded index words; reason: the source algorithm uses ring operations; the reduction must prove its integer simulation with the allowed polylogarithmic overhead, with no integer-simulation hypothesis
--   - encoding: finite sets and set families → arbitrary-order duplicate-free lists, with subset masks on Fin d; reason: every finite-set instance has such a presentation; no sorting or disjointness promise is added and all presentation and output costs are charged
--   - encoding: natural subset rank parameter t and d=ceil(t+lg nhat+lg lg N+1) with soft-O time → all natural t below lg nhat, the same real ceiling, and a uniform power of 1+lg(max(2,N)); reason: the parameter inequality implies positive sides, nhat>1 and N>=3, so every displayed logarithm and denominator is in its source domain
--   - encoding: Monte Carlo total time and O(1/N) error → one finite fair-bit program for each fixed magnitude exponent, a size-dependent worst-case budget, and a measurable event that any Boolean output is incorrect or the run rejects; reason: the source allows truncation and amplification; every tape must halt and the joint event includes all queries, with actual sampling, preprocessing and output writes charged
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 2.3, pp.6–7; proof, truncation and joint-error amplification, pp.7–9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_AllQueries

namespace SelectedSubset3SUM.Integer

/-- Theorem 2.3, pp.6--7: full three-term reduction, with all real weights retained
in its conditional premise. Ring-arithmetic simulation on the bounded integer instances
is a proof obligation, not a hypothesis about the input or the solver's success. -/
theorem theorem_2_3 (P Q : ℕ → ℕ → ℕ → ℝ) (hsolver : RealSubsetSolver P Q) :
    ∀ κ : ℕ, ∃ (code : List TrulySubcubicAPSP.Instr) (b e : ℕ) (K : ℝ)
      (T : ℕ → ℕ → ℕ → ℕ → ℕ),
      0 < b ∧ 0 < K ∧
      ∀ (I : SumInput) (t : ℕ), I.Valid κ → (t : ℝ) < lg I.nhat →
        (sumCharge t (T I.A.length I.B.length I.C.length t) I : ℝ) ≤
          K * polylogFactor I.N e * reductionCost P Q I t ∧
        ∀ W ≥ b * (Nat.log2 (max 2 I.N) + 1),
          MonteCarloAt code W t (T I.A.length I.B.length I.C.length t) K I := by sorry

end SelectedSubset3SUM.Integer

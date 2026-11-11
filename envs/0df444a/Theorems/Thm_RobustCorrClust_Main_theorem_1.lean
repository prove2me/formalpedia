-- Prove2me | Theorems.Thm_RobustCorrClust_Main_theorem_1
-- name    : RobustCorrClust.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:25.415082+00:00
-- url     : https://prove2.me/theorems/bbb04007-e41f-4fbe-97ef-d0fca7a538c2
-- title:
--   Theorem 1 — a randomized single-pass streaming algorithm with expected cost ≤ (2.414 + ε)·OPT against adaptive adversaries, Õ(n/ε²) space, polynomial time
-- statement:
--   Correlation clustering on a vertex set $\{0,\dots,n-1\}$ of known size: the positive pairs arrive one at a time in an insertion-only stream chosen by an adversary that sees all previous outputs, and after any insertion a clustering may be requested; its cost is measured on the current graph $G_\sigma$ (inserted pairs positive, all other pairs negative).
--
--   The model is a randomized logarithmic-cost RAM (integer cells, a fair coin, every instruction charged its operand bit lengths) whose memory persists between calls; space is the total bit length of the addresses and contents of the nonzero cells.
--
--   **Theorem 1.** There are one program $P$ and constants $C>0$, $k\in\mathbb N$ such that for every $n$ and every $\varepsilon=p/q$ with integers $1\le p\le q$:
--
--   - **(space)** at every step of the initialisation call on $(n,p,q)$, and of every insertion or request call made from a memory reachable after a valid operation sequence, on every random tape,
--   $$\text{space}\le C\,(n+1)\,\varepsilon^{-2}\,\big(\log_2(n+q+2)\big)^k\ \text{bits};$$
--   - **(time)** for every $(p,q)$ there is $k'$ such that every such call halts on every random tape with log-cost at most $(n+2)^{k'}$;
--   - **(approximation)** for every valid sequence $\sigma$ and every memory $m$ reachable after $\sigma$, a request call from $m$ halts within a bounded number of steps and the clustering $\mathcal C$ it outputs satisfies
--   $$\mathbb E\big[\mathrm{cost}_{G_\sigma}(\mathcal C)\big]\le(2.414+\varepsilon)\,\mathrm{OPT}(G_\sigma),$$
--   the expectation over the request call's fresh coins.
--
--   Since the guarantee holds from every reachable memory, it holds conditionally on any history, hence against any adaptive adversary.
--
--   Differences from the source:
--   - encoding: "a (randomized) streaming algorithm" → one program of the randomized log-cost RAM with persistent memory and the call interface of `StreamingRAM`; reason: the paper's machine is informal, and this one gives the stream only through calls.
--   - reading: "$\tilde O(n/\varepsilon^2)$ words of total memory (including post-processing)" with words of $O(\log(n/\varepsilon))$ bits (§3.2) → at most $C(n+1)\varepsilon^{-2}(\log_2(n+q+2))^k$ bits at every step of every call, addresses charged, $C,k$ fixed before $n,\varepsilon$; reason: a word count is vacuous on a real RAM (INSIGHTS I1), and the paper's precision is $O(\log(n/\varepsilon))$ bits.
--   - reading: "given any parameter $\varepsilon$" → $\varepsilon=p/q\in(0,1]$ given as integers $1\le p\le q$; reason: for $\varepsilon>1$ the space bound would fall below the $\Omega(n)$ output size (p. 3), and a machine reads integers.
--   - reading: "polynomial time per update in $n$, for each fixed $\varepsilon$" → for each $(p,q)$ an exponent $k'$ with every call (initialisation, insertion, request) halting on every random tape within $(n+2)^{k'}$ log-cost; reason: worst-case time per call, the paper's post-processing included.
--   - generalization: "against an adaptive adversary … expected cost … whenever a clustering is requested" → the expected cost bound from every memory reachable after every valid sequence, over the request's fresh coins; reason: this is the paper's own argument (p. 54) and implies the guarantee against every adaptive adversary.
--   - encoding: the expectation over the request's coins → the average over the $2^K$ values of the first $K$ coins, for every $K$ within which the request call halts on every tape; reason: such a call reads at most $K$ coins, so this is the exact expectation.
--   - encoding: $2.414$ → $2414/1000$; reason: the same number.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 3, Theorem 1 (restated p. 49; proof p. 54)

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_RobustCorrClust_Main_StreamingRAM

open SubsetSumPartialMatch.SubsetSum

namespace RobustCorrClust.Main

/-- Theorem 1 (p. 3; restated p. 49, proved p. 54). There are one program `P` of the randomized
log-cost RAM and constants `C > 0`, `k ∈ ℕ` such that, for every `n` and every `ε = p/q` with
integers `1 ≤ p ≤ q`:
(a) space: at every step of the initialisation call and of every later call (insertion or request)
made from a reachable memory on a valid sequence, on every random tape, the memory occupies at
most `C (n+1) ε⁻² (log₂(n + q + 2))^k` bits;
(b) time: for every `(p, q)` there is `k'` such that every such call halts, on every random tape,
with log-cost at most `(n+2)^{k'}`;
(c) approximation: from every memory reachable after a valid sequence `σ`, a request call halts
within a bounded number of steps and the expected cost (over its fresh coins) of the clustering
it outputs is at most `(2.414 + ε) · OPT(G_σ)`. -/
theorem theorem_1 :
    ∃ P : Program, ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      (∀ n p q : ℕ, 1 ≤ p → p ≤ q →
        (∀ (ω : ℕ → Bool) (t : ℕ),
          SpaceLE (callRun P ω (loadInit n p q zeroMem) t).mem
            (C * ((n : ℝ) + 1) * ((q : ℝ) / p) ^ 2 * Real.logb 2 ((n : ℝ) + q + 2) ^ k)) ∧
        ∀ (σ : List Op) (m : ℕ → ℤ) (op : Op), Valid n (σ ++ [op]) → Reach P n p q σ m →
          ∀ (ω : ℕ → Bool) (t : ℕ),
            SpaceLE (callRun P ω (loadOp op m) t).mem
              (C * ((n : ℝ) + 1) * ((q : ℝ) / p) ^ 2 * Real.logb 2 ((n : ℝ) + q + 2) ^ k)) ∧
      (∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ k' : ℕ, ∀ n : ℕ,
        (∀ ω : ℕ → Bool, ∃ t, Halted P (callRun P ω (loadInit n p q zeroMem) t) ∧
          ((callRun P ω (loadInit n p q zeroMem) t).cost : ℝ) ≤ ((n : ℝ) + 2) ^ k') ∧
        ∀ (σ : List Op) (m : ℕ → ℤ) (op : Op), Valid n (σ ++ [op]) → Reach P n p q σ m →
          ∀ ω : ℕ → Bool, ∃ t, Halted P (callRun P ω (loadOp op m) t) ∧
            ((callRun P ω (loadOp op m) t).cost : ℝ) ≤ ((n : ℝ) + 2) ^ k') ∧
      (∀ n p q : ℕ, 1 ≤ p → p ≤ q →
        ∀ (σ : List Op) (m : ℕ → ℤ), Valid n σ → Reach P n p q σ m →
          (∃ K, HaltsWithin P (loadOp Op.request m) K) ∧
          ∀ K, HaltsWithin P (loadOp Op.request m) K →
            expOutCost P (graphOf n σ) (loadOp Op.request m) K ≤
              (2414 / 1000 + (p : ℝ) / q) * (OPT (graphOf n σ) : ℝ)) := by sorry

end RobustCorrClust.Main

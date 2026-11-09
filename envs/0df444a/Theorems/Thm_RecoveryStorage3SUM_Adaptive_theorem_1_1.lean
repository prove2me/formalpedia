-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_theorem_1_1
-- name    : RecoveryStorage3SUM.Adaptive.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:43.676977+00:00
-- url     : https://prove2.me/theorems/d4ab8d22-6694-4db3-a650-8a2d0b02f6f2
-- title:
--   Theorem 1.1 — preprocessed 3SUM with unknown $C$: $\widetilde O(n^{2-\epsilon})$ space, $\widetilde O(n^{3/2+\epsilon})$ worst-case query time
-- statement:
--   Fix $\epsilon\in[0,1/2]$, a polynomial bound $H(n+2)^\kappa$ with $H\ge1$ on all integers, a constant $q\ge1$ with $|C'|\le qn$, and a failure exponent $d>0$. There are a word width $O(\log n)$, a randomized preprocessing program, a deterministic query program, and constants $C,e$, such that for every $n$ and all sets $A,B$ of $n$ bounded integers:
--
--   1. on every coin sequence, the preprocessing, receiving only $n,A,B$, halts within $C(n+2)^2\log^e(n+2)$ steps and stores at most $C(n+2)^{2-\epsilon}\log^e(n+2)$ bits;
--   2. except with probability $(n+2)^{-d}$ over the coins of the preprocessing, every legal query $(A',B',C')$, with $A'\subseteq A$, $B'\subseteq B$, and $C'$ a set of at most $qn$ bounded integers, is answered correctly within
--   $$C(n+2)^{3/2+\epsilon}\log^e(n+2)$$
--   steps, simultaneously for all such queries.
--
--   An answer states whether some $a\in A'$, $b\in B'$ have $a+b\in C'$, and for each $c\in C'$ whether some $a+b=c$. This is the headline tradeoff: it improves the prior space bound $\widetilde O(n^{2-2\epsilon/3})$ at the same query time, and the single success event means that queries may be chosen adaptively.
--
--   **Formalization Note** The programs are finite instruction lists, and all time bounds refer to their RAM executions. Choosing and computing integer parameters, handling $n=0,1$, and using the direct pair-scan branch at $\epsilon=1/2$ remain implementation obligations of the theorem. The goal assumes neither successful inversion nor recovery, load checks, or clean runs.
--
--   Differences from the source:
--   - generalization: "every query is answered correctly": one 3SUM decision → the decision and one answer per target; reason: Algorithm 3 outputs an answer for every $c\in C$; the decision is one of the stated outputs
--   - generalization: asymptotic bounds and "w.h.p." for large $n$ → all $n\ge0$, with failure at most $(n+2)^{-d}$; reason: below a threshold a direct pair scan is exact; large $n$ gives the sources claim
--   - reading: "with high probability" → for every fixed $d>0$, failure at most $(n+2)^{-d}$; programs and constants may depend on $d$; reason: pp.10-13 give tunable polynomial tails
--   - reading: "preprocessing runs in $\widetilde O(n^2)$ time and occupies space $\widetilde O(n^{2-\epsilon})$" → both on every coin sequence; reason: the theorem attaches no probability to them; the attempt loop is capped
--   - reading: "randomized data structure" → the query program has no coin instructions; reason: p.5: "the query procedure is deterministic"
--   - encoding: word RAM with $O(\log n)$-bit words → the published machine, width $b(\lfloor\log_2(n+2)\rfloor+1)$; reason: the source fixes no instruction list; this one has arithmetic, indirect addressing and branching
--   - encoding: space in words → space in bits of the stored string; reason: bits and $O(\log n)$-bit words differ by a logarithmic factor
--   - encoding: polynomially bounded integers, $|C|=O(n)$ → $H\ge1$, $\kappa\in\mathbb N$, $q\ge1$ fixed before the programs; reason: the theorem holds for each polynomial bound
--   - encoding: $\widetilde O(n^\alpha)$ → $C(n+2)^\alpha\log^e(n+2)$; reason: positive at $n\le 1$; for large $n$ the same class
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MatroidSensOracle in
/-- Theorem 1.1, p.2. Fix `ε ∈ [0, 1/2]`, a polynomial bound `H (n + 2)^κ` on all integers, a multiplier
`q` with `|C′| ≤ q n`, and a failure exponent `d > 0`. There are a word width `b log n`, a preprocessing
program, a coin-free query program, and constants such that on every legal `(A, B)`:

* on every coin sequence, the preprocessing halts within `Õ(n²)` steps and stores `Õ(n^{2-ε})` bits;
* except with probability `(n + 2)^{-d}` over the coins, **all** legal queries are simultaneously
  answered correctly, each within `Õ(n^{3/2+ε})` steps.

The programs receive only the instance and query encodings; no real-power or inversion oracle is
available. Choosing and computing construction parameters, including rounding, finite exceptions,
and the direct-query endpoint `ε = 1/2`, is part of the theorem's implementation obligation. -/
theorem theorem_1_1 (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 2) (H κ q : ℕ)
    (hH : 1 ≤ H) (hq : 1 ≤ q) (d : ℝ) (hd : 0 < d) :
    ∃ (b e : ℕ) (C : ℝ) (D : Oracle), 0 < b ∧ 0 < C ∧ CoinFree D.query ∧
      ∀ (n : ℕ) (as bs : List ℤ), LegalInput H κ n as bs →
        D.PrepWithin (wordWidth b n) (prepInput as bs) (softSteps C 2 e n)
            (softBound C (2 - ε) e n) ∧
          coinLaw {ω : Coins | ¬ PreprocessingSucceeds D H κ q n (wordWidth b n)
              (softSteps C 2 e n) (softSteps C (3 / 2 + ε) e n) as bs ω} ≤
            ENNReal.ofReal (((n : ℝ) + 2) ^ (-d)) := by sorry

end RecoveryStorage3SUM.Adaptive

-- Prove2me | Theorems.Thm_ReadTwiceCount_lemma_7_1
-- name    : ReadTwiceCount.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:32.611206+00:00
-- url     : https://prove2.me/theorems/9655e65f-a8fc-47e6-be56-2e3e74b91e1f
-- title:
--   Lemma 7.1 — total work $T(s,a)\le AP(N)a^{-k}(s+1)q^{ks}$
-- statement:
--   **Lemma 7.1.** For a suitable absolute constant $A$, the total number of operations in an active call satisfies
--   $$T(s,a)\le A\,P(N)\,a^{-k}(s+1)q^{ks}.$$
--
--   Precisely: there is $A$ such that for every $n\ge1$, $k\ge2$, $P\ge0$, every read-twice normalized state $H$ with $s\le n$ clauses, every positive dangling query $h$, every density $0<a<1$ and every run of $\mathrm{Solve}(H,h,a)$, if each call of the run has nonrecursive cost at most $P\,a_{\text{call}}^{-k}$ (30), then the sum of the costs over all calls of the run (each call counted separately) is at most $A\,P\,a^{-k}(s+1)q^{ks}$, with $q=1+\frac1{10n}$ (17).
--
--   Since $q^{kn}\le e^{k/10}$, the number of calls and operations is polynomial in $N$ and the reciprocal initial density.
--
--   Differences from the source:
--   - reading: "the total number of operations in an active call" under (30) → the sum, over all calls of the run tree, of a per-call cost bounded by $P\,a_{\text{call}}^{-k}$ at every call, with $P=P(N)\ge0$ and $k\ge2$; $A$ chosen before everything else; reason: the paper's proof counts exactly this (30)-bounded nonrecursive work per call and sums it over the calls; the operation model itself is carried by Theorem 1.1's machine bound
--   - generalization: the marginal procedure (a fixed expansion order and dyadic $r_i$) → every run of the procedure; reason: the paper's procedure produces one of these runs, and the proof uses only (31)–(32), $s_i+1\le s$ and (30)
--   - reading: an active call with global $n$ → hypotheses $n\ge1$, $s\le n$, $0<a<1$, read-twice normalized positive dangling $(H,h)$; reason: the standing context of §5 and §7.1 ("For active calls with $0<a<1$")
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 7.1, display (33), p.11; (30), p.11

import Mathlib
import Definitions.Def_ReadTwiceCount_SolveRun

namespace ReadTwiceCount

/-- **Lemma 7.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Lemma 7.1, p.11): "For a suitable absolute
constant A, the total number of operations in an active call satisfies T(s, a) ≤ AP(N)a^{−k}(s + 1)q^{ks}."
(33)

Under (30), every call of the run costs at most `P a^{−k}` nonrecursive operations; the lemma bounds
the total over all calls of the run of an active call (`0 < a < 1`) on an `s`-clause positive dangling
query, with `q = 1 + 1/(10n)` (17).

**Formalization Note** "Total number of operations" is the sum, over the calls of the run tree (each
call counted separately), of a per-call nonrecursive cost `cost` that is bounded by `P·a_call^{−k}`
at every call (the paper's (30), with `P = P(N)` a nonnegative number and `k ≥ 2`). `A` is chosen
before `n`, `k`, `P`, the state and the run. -/
theorem lemma_7_1 :
    ∃ A : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 2 ≤ k → ∀ (P : ℝ), 0 ≤ P →
      ∀ {M : ℕ} (H : Formula M) (h : Lit M) (a U : ℚ) (R : SolveRun n H h a U),
        0 < a → a < 1 → ReadTwice H → Normalized H → IsDangling H h → IsPositive H h →
        H.clauses.length ≤ n →
        ∀ cost : (H' : Formula M) → (h' : Lit M) → (a' U' : ℚ) → SolveRun n H' h' a' U' → ℝ,
          R.AllCalls (fun H' h' a' U' R' => cost H' h' a' U' R' ≤ P * ((a' : ℝ)⁻¹) ^ k) →
          R.totalCost cost ≤
            A * P * ((a : ℝ)⁻¹) ^ k * ((H.clauses.length : ℝ) + 1) *
              qFactor n ^ (k * H.clauses.length) := by sorry

end ReadTwiceCount

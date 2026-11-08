-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_theorem_1
-- name    : QRetrieval.Adaptive.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:52.685318+00:00
-- url     : https://prove2.me/theorems/759440f1-3dbe-4b86-b197-76aa3c4f6df1
-- title:
--   Theorem 1 — $s_Q(m,n,t)=O\bigl(n^{1-1/t}m^{1/t}(\log(m/n))^{1-1/t}\bigr)$
-- statement:
--   There is an absolute constant $C$ such that for all natural numbers $m,n,t$ with $n\ge1$, $n\le m/2$ and $t\ge1$ there is a valid $(m,n,s,t)$-compression scheme with
--
--   $$
--   s\ \le\ C\, n^{1-1/t}\, m^{1/t}\,\bigl(\log_2(m/n)\bigr)^{1-1/t}.
--   $$
--
--   That is, every $m$-bit string of Hamming weight at most $n$ can be stored in $s=O\bigl(n^{1-1/t}m^{1/t}(\log(m/n))^{1-1/t}\bigr)$ bits so that each of its bits is recovered **with certainty** by a quantum circuit that may depend on the index but not on the string, makes at most $t$ adaptive queries to the phase oracle $O_y$ of the stored string $y$, and measures once at the end.
--
--   The bound is within a factor $\log(m/n)/t$ of the lower bound $s_Q(m,n,t)=\Omega(t\,n^{1-1/t}m^{1/t})$ (valid for $t\le\log(m/n)$), and for $t=\Omega(\log(m/n))$ it becomes $O(n\log(m/n))$, which matches the information-theoretic lower bound $\log\binom{m}{n}$.
--
--   **Formalization Note** Powers are real powers of positive reals, and divisions are real. The scheme is a `CompressionScheme m n s t` and validity is exact (`= 1`).
--
--   Differences from the source:
--   - reading: (log(m/n)^{1−1/t}) → (Real.logb 2 (m/n)) ^ (1 − 1/t); reason: the proof's last line (p. 11) writes log^{1−1/t}(m/n) and Theorem 2 (p. 2) writes (log(m/n))^{1−1/t}; the other parse is 0 at t = 1, where the claim would be false
--   - encoding: s_Q(m, n, t) = O(n^{1−1/t} m^{1/t} (log(m/n))^{1−1/t}) (O(·), log of unspecified base) → ∃ C : ℝ chosen before every variable; log = Real.logb 2; reason: an absolute constant is what O(·) means here; the base of the logarithm only changes C
--   - encoding: For all m, n ≤ m/2 and t → 1 ≤ n, 2 * n ≤ m, 1 ≤ t; reason: log(m/n) and 1/t are undefined at n = 0 and t = 0
--   - encoding: s_Q(m, n, t) ≤ X, s_Q the smallest s with a valid scheme → ∃ s, (s : ℝ) ≤ X ∧ ∃ S : CompressionScheme m n s t, S.Valid; reason: equivalent since s_Q is a minimum over a nonempty set; avoids sInf ∅ = 0
--   - encoding: Definition 2.1's circuit: unitaries controlled by the index register, at most t oracle gates O_y, a final measurement with outcome in {0,1} → one QueryAlg per index i with shared work register W and T ≤ t queries, controlledPhaseOracle, computational-basis measurement followed by out i; reason: the same class of circuits (an I-controlled unitary is one unitary per value of I; a two-outcome projective measurement is a basis change folded into U_T)
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Theorem 1, p. 1 (proof §4, pp. 10–11)

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_CompressionScheme

namespace QRetrieval.Adaptive

/-- **Theorem 1: `s_Q(m, n, t) = O(n^{1−1/t} m^{1/t} (log(m/n))^{1−1/t})`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Theorem 1, p. 1: "For all `m`, `n ≤ m/2` and `t`, we have
`s_Q(m, n, t) = O(n^{1−1/t} m^{1/t} (log(m/n)^{1−1/t}))`", where (p. 1, Definition 2.1 p. 4)
`s_Q(m, n, t)` is the smallest `s` such that a valid `(m, n, s, t)`-compression scheme exists.

There is an absolute constant `C` such that for all `m, n, t` with `n ≥ 1`, `2n ≤ m` and `t ≥ 1`
there is a valid `(m, n, s, t)`-compression scheme (`CompressionScheme m n s t`, exact retrieval
of every bit of every `x ∈ B(m, n)` with at most `t` adaptive queries to `O_{f(x)}`) with
`s ≤ C · n^{1−1/t} · m^{1/t} · (log₂(m/n))^{1−1/t}`.

**Formalization Note.**
1. "(log(m/n)^{1−1/t})" is read as `(log(m/n))^{1−1/t}`, as in the last line of the proof
   (p. 11, `log^{1−1/t}(m/n)`) and Theorem 2 (p. 2).
2. `O(·)` is an absolute constant `C` chosen before `m, n, t`; `log = log₂` (the proof, p. 10,
   uses `r ≥ 64 ⇒ L ≥ 6`); the base only changes `C`. Powers are real powers (`Real.rpow`) of
   positive reals, and divisions are real.
3. `n ≥ 1` and `t ≥ 1`, because `log(m/n)` and `1/t` are undefined at `n = 0`, `t = 0`.
4. `s_Q(m, n, t) ≤ X` is stated as the existence of a valid scheme with `s ≤ X`, which is
   equivalent (`s_Q` is a minimum over a nonempty set) and avoids `sInf ∅ = 0`. -/
theorem theorem_1 : ∃ C : ℝ, ∀ m n t : ℕ, 1 ≤ n → 2 * n ≤ m → 1 ≤ t →
    ∃ s : ℕ, (s : ℝ) ≤ C * (n : ℝ) ^ (1 - 1 / (t : ℝ)) * (m : ℝ) ^ (1 / (t : ℝ)) *
        (Real.logb 2 ((m : ℝ) / n)) ^ (1 - 1 / (t : ℝ)) ∧
      ∃ S : CompressionScheme m n s t, S.Valid := by sorry

end QRetrieval.Adaptive

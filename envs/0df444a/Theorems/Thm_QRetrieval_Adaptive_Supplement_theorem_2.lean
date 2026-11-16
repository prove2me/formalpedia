-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_Supplement_theorem_2
-- name    : QRetrieval.Adaptive.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:59:24.389127+00:00
-- url     : https://prove2.me/theorems/f228e085-9798-4253-8e3b-865d636b980d
-- title:
--   Theorem 2 — $s_{QN}(m,n,t)=O\bigl(t\,n^{2(1-1/t)}m^{1/t}(\log(m/n))^{1-1/t}\bigr)$
-- statement:
--   For natural numbers $m,n,t$ let $s_{QN}(m,n,t)$ be the least length $s$ of a stored string for which there is a valid $(m,n,s,t)$-compression scheme with **non-adaptive** quantum retrieval: every $x\in\{0,1\}^m$ of Hamming weight at most $n$ is stored as $y=f(x)\in\{0,1\}^s$, and every bit $x_i$ is recovered with probability $1$ by a fixed quantum circuit that makes at most $t$ probes into $y$, all in parallel through one product oracle gate $O_y^{\otimes t'}$, $t'\le t$.
--
--   There is an absolute constant $C$ such that for all $m,n,t$ with $1\le n\le m/2$ and $t\ge1$ there is a valid non-adaptive $(m,n,s,t)$-compression scheme with
--
--   $$
--   s\ \le\ C\cdot t\cdot n^{2(1-1/t)}\cdot m^{1/t}\cdot\bigl(\log_2(m/n)\bigr)^{1-1/t},
--   $$
--
--   that is, $s_{QN}(m,n,t)=O\bigl(t\,n^{2(1-1/t)}m^{1/t}(\log(m/n))^{1-1/t}\bigr)$.
--
--   This is the non-adaptive counterpart of the paper's Theorem 1: the dependence on $m$ is the optimal $m^{1/t}$ (up to the logarithmic factor), at the price of a worse polynomial in $n$ and a factor $t$.
--
--   **Formalization Note** The constant $C$ is chosen before $m,n,t$; $\log$ is $\log_2$; powers are real powers. $s_{QN}\le X$ is stated as the existence of a valid non-adaptive scheme with $s\le X$, which avoids an infimum of a possibly empty set. The scheme is `NonAdaptiveCompressionScheme m n s t` with `Valid`.
--
--   Differences from the source:
--   - encoding: $s_{QN}(m,n,t)=O(\cdot)$ (O of unspecified constant, log of unspecified base) → $\exists C:\mathbb R$ chosen before $m,n,t$, with $\log=\log_2$; reason: an absolute constant is what $O(\cdot)$ means here, and the proof (p. 12) uses $L=\log_2(m/n)$; the base only changes $C$
--   - encoding: for all $m$, $n\le m/2$ and $t$ → $1\le n$, $2n\le m$, $1\le t$; reason: $\log(m/n)$ is undefined at $n=0$ and $1/t$ at $t=0$
--   - encoding: $s_{QN}(m,n,t)\le X$ (a minimum) → $\exists s\le X$ with a valid non-adaptive $(m,n,s,t)$-scheme; reason: equivalent, since the minimum is over a nonempty set of naturals
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Theorem 2, p. 2 (proof §4, p. 12)

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_Supplement_NonAdaptiveCompressionScheme

namespace QRetrieval.Adaptive.Supplement

/-- **Theorem 2: `s_QN(m, n, t) = O(t n^{2(1−1/t)} m^{1/t} (log(m/n))^{1−1/t})`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Theorem 2, p. 2 (proof §4, p. 12): "For all `m`, `n ≤ m/2` and `t`, we have
`s_QN(m, n, t) = O(t n^{2(1−1/t)} m^{1/t} (log(m/n))^{1−1/t})`", where (Definition 2.1, p. 4)
`s_QN(m, n, t)` is the smallest `s` such that a valid `(m, n, s, t)`-compression scheme with
non-adaptive query scheme exists.

There is an absolute constant `C` such that for all `m, n, t` with `n ≥ 1`, `2n ≤ m` and `t ≥ 1`
there is a valid non-adaptive `(m, n, s, t)`-compression scheme with
`s ≤ C · t · n^{2(1−1/t)} · m^{1/t} · (log₂(m/n))^{1−1/t}`.

**Formalization Note.**
1. `O(·)` is an absolute constant `C` chosen before `m, n, t`; `log = log₂` (the proof, p. 12,
   writes `L = log₂(m/n)`); powers are real powers (`Real.rpow`) of nonnegative reals and the
   division `m/n` is real.
2. `n ≥ 1` and `t ≥ 1`, because `log(m/n)` and `1/t` are undefined at `n = 0`, `t = 0`.
3. `s_QN(m, n, t) ≤ X` is stated as the existence of a valid non-adaptive scheme with `s ≤ X`
   (equivalent, since `s_QN` is a minimum over a nonempty set; avoids `sInf ∅ = 0`).
4. No rounding hypothesis: `m^{1/t}`, `m/m₁` need not be integers (the proof omits rounding,
   p. 12). -/
theorem theorem_2 : ∃ C : ℝ, ∀ m n t : ℕ, 1 ≤ n → 2 * n ≤ m → 1 ≤ t →
    ∃ s : ℕ, (s : ℝ) ≤ C * (t : ℝ) * (n : ℝ) ^ (2 * (1 - 1 / (t : ℝ))) * (m : ℝ) ^ (1 / (t : ℝ)) *
        (Real.logb 2 ((m : ℝ) / n)) ^ (1 - 1 / (t : ℝ)) ∧
      ∃ S : NonAdaptiveCompressionScheme m n s t, S.Valid := by sorry

end QRetrieval.Adaptive.Supplement

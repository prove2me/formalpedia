-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_Supplement_theorem_8
-- name    : QRetrieval.Adaptive.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:59:59.510009+00:00
-- url     : https://prove2.me/theorems/2f0730f4-9807-4811-91a4-47f40d9e3b22
-- title:
--   Theorem 8 — $s_{QN}(m,n,t)=O(t\,2^n m^{1/t})$
-- statement:
--   For natural numbers $m,n,t$ let $s_{QN}(m,n,t)$ be the least length $s$ of a stored string for which there is a valid $(m,n,s,t)$-compression scheme with **non-adaptive** quantum retrieval: every $x\in\{0,1\}^m$ of Hamming weight at most $n$ is stored as $y=f(x)\in\{0,1\}^s$, and every bit $x_i$ is recovered with probability $1$ by a fixed quantum circuit that makes at most $t$ probes into $y$, all in parallel through one product oracle gate $O_y^{\otimes t'}$, $t'\le t$.
--
--   There is an absolute constant $C$ such that for all $m$, all $n$ and all $t\ge1$ there is a valid non-adaptive $(m,n,s,t)$-compression scheme with
--
--   $$
--   s\ \le\ C\cdot t\cdot 2^{n}\cdot m^{1/t},
--   $$
--
--   that is, $s_{QN}(m,n,t)=O(t\,2^n m^{1/t})$.
--
--   For constant $n$ this is compression to $O(t\,m^{1/t})$ bits, which has the optimal dependence on $m$ and no $\log(m/n)$ factor.
--
--   **Formalization Note** The constant $C$ is chosen before $m,n,t$, and $m^{1/t}$ is a real power; the statement is not restricted to perfect $t$-th powers $m$ (footnote 3, p. 13, ignores rounding). No hypothesis is put on $m$ or $n$. Section 5 stores sets $S\subseteq[m]$ of size at most $n$; these are the supports of the strings $x\in B(m,n)$, with $x_i=1$ iff $i\in S$.
--
--   Differences from the source:
--   - encoding: $s_{QN}(m,n,t)=O(t2^nm^{1/t})$ (O of unspecified constant) → $\exists C:\mathbb R$ chosen before $m,n,t$; reason: an absolute constant is what $O(\cdot)$ means here
--   - encoding: for all $m,n,t$ → $1\le t$; reason: $m^{1/t}$ is undefined at $t=0$
--   - encoding: $s_{QN}(m,n,t)\le X$ (a minimum) → $\exists s\le X$ with a valid non-adaptive $(m,n,s,t)$-scheme; reason: equivalent, since the minimum is over a nonempty set of naturals
--   - encoding: sets $S\subseteq[m]$ with $|S|\le n$, membership queries → strings $x\in B(m,n)$, bit queries $x_i$; reason: $S$ is the support of $x$; the same data and the same answers
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Theorem 8, §5, p. 12 (proof pp. 12–13)

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_Supplement_NonAdaptiveCompressionScheme

namespace QRetrieval.Adaptive.Supplement

/-- **Theorem 8: `s_QN(m, n, t) = O(t 2^n m^{1/t})`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Theorem 8, §5 (Non-adaptive scheme for small `n`), p. 12 (proof pp. 12–13):
"`s_QN(m, n, t) = O(t2^n m^{1/t})`", where (Definition 2.1, p. 4) `s_QN(m, n, t)` is the smallest
`s` such that a valid `(m, n, s, t)`-compression scheme with non-adaptive query scheme exists.

There is an absolute constant `C` such that for all `m, n` and all `t ≥ 1` there is a valid
non-adaptive `(m, n, s, t)`-compression scheme with `s ≤ C · t · 2^n · m^{1/t}`.

**Formalization Note.**
1. `O(·)` is an absolute constant `C` chosen before `m, n, t`; `m^{1/t}` is a real power
   (`Real.rpow`). Footnote 3 (p. 13) ignores that `m^{1/t}` need not be an integer; the statement
   is not restricted to perfect `t`-th powers.
2. The theorem carries no hypothesis on `m` or `n` (in particular not `n ≤ m/2`); only `t ≥ 1`,
   because `1/t` is undefined at `t = 0`.
3. `s_QN(m, n, t) ≤ X` is stated as the existence of a valid non-adaptive scheme with `s ≤ X`.
4. §5 speaks of sets `S ⊆ [m]` of size at most `n`; these are the supports of the strings
   `x ∈ B(m, n)`, and membership `x ∈ S` is the bit `x_i`. -/
theorem theorem_8 : ∃ C : ℝ, ∀ m n t : ℕ, 1 ≤ t →
    ∃ s : ℕ, (s : ℝ) ≤ C * (t : ℝ) * (2 : ℝ) ^ n * (m : ℝ) ^ (1 / (t : ℝ)) ∧
      ∃ S : NonAdaptiveCompressionScheme m n s t, S.Valid := by sorry

end QRetrieval.Adaptive.Supplement

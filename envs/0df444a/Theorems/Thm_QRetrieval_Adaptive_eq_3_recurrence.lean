-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_eq_3_recurrence
-- name    : QRetrieval.Adaptive.eq_3_recurrence
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:47.390697+00:00
-- url     : https://prove2.me/theorems/323a5781-e327-4bf8-ab18-010303509953
-- title:
--   Eq. (3) — the recurrence $s_Q(m,n,t)\le Cm_1\log(m_1/n)+s_Q(m'',n,t-1)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $t\ge2$, and $2n\le m_1\le m$, and let $m''\ge 2n\lceil m/m_1\rceil$. If there is a valid $(m'',n,s',t-1)$-compression scheme, then there is a valid $(m,n,s,t)$-compression scheme with
--
--   $$
--   s\ \le\ C\,m_1\log_2(m_1/n)+s' .
--   $$
--
--   In terms of $s_Q$ this is the recurrence $s_Q(m,n,t)\le C m_1\log(m_1/n)+s_Q(m'',n,t-1)$: the second memory $M_2$ of Lemma 6 (after padding $x$ with zeros to a multiple of $m_1$, length at most $m'=m+m_1$) has weight at most $n$, so it can be stored with a $(t-1)$-query scheme instead of being read by a classical probe. The condition $2n\le m_1\le m'/2$ that Lemma 6 needs is $2n\le m_1\le m$.
--
--   **Formalization Note** $s_Q$ is not defined; the inequality is stated for every achievable $s'$. The constant $C$ does not depend on $t$, since the proof of Theorem 1 applies the recurrence $t-1$ times with the same $C$.
--
--   Differences from the source:
--   - encoding: s_Q(m, n, t) ≤ C m1 log(m1/n) + s_Q(m″, n, t − 1) → for every s′ with a valid (m″, n, s′, t − 1)-scheme there is a valid (m, n, s, t)-scheme with s ≤ C m₁ log₂(m₁/n) + s′; reason: s_Q is the least achievable length, so the two forms are equivalent; avoids sInf
--   - generalization: m″ ≤ 2n(m′/m1) = 2n((m + m1)/m1), the length of M2 after padding → every m″ ≥ 2n⌈m/m₁⌉; reason: m″ = 2n⌈m/m1⌉ ≤ 2n(m + m1)/m1 is the paper's length; longer m″ are also allowed (pad M2 with zeros)
--   - encoding: 2n ≤ m1 ≤ m′/2 with m′ = m + m1 → 2 * n ≤ m₁ and m₁ ≤ m; reason: m1 ≤ (m + m1)/2 is equivalent to m1 ≤ m
--   - encoding: C m1 log(m1/n) (O(·), log of unspecified base) → ∃ C : ℝ chosen before every variable; log = Real.logb 2; reason: an absolute constant is what O(·) means here; the base of the logarithm only changes C
--   - encoding: (implicit) the recurrence is applied while probes remain → 1 ≤ n and 2 ≤ t; reason: log(m1/n) is undefined at n = 0, and t − 1 ≥ 1 queries are needed for the inner scheme
--   - encoding: Definition 2.1's circuit: unitaries controlled by the index register, at most t oracle gates O_y, a final measurement with outcome in {0,1} → one QueryAlg per index i with shared work register W and T ≤ t queries, controlledPhaseOracle, computational-basis measurement followed by out i; reason: the same class of circuits (an I-controlled unitary is one unitary per value of I; a two-outcome projective measurement is a basis change folded into U_T)
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §4, proof of Theorem 1, Eq. (3), p. 10

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_CompressionScheme

namespace QRetrieval.Adaptive

/-- **Eq. (3): the recurrence `s_Q(m, n, t) ≤ C m1 log(m1/n) + s_Q(m″, n, t − 1)`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §4, proof of Theorem 1, Eq. (3), p. 10: "pad the input string by zeros so that
its length is divisible by `m1`; the new string will have length at most `m′ = m + m1`. We may
then write the recurrence `s_Q(m, n, t) ≤ C m1 log(m1/n) + s_Q(m″, n, t − 1)`, (3) where
`m″ ≤ 2n(m′/m1) = 2n((m + m1)/m1)`. However, to use Lemma 6 we need to ensure that
`2n ≤ m1 ≤ m′/2`."

There is an absolute constant `C` such that for all `n ≥ 1`, `t ≥ 2`, `m1` with `2n ≤ m1 ≤ m`,
and every `m″ ≥ 2n⌈m/m1⌉`: if a valid `(m″, n, s′, t − 1)`-scheme exists, then a valid
`(m, n, s, t)`-scheme exists with `s ≤ C · m1 · log₂(m1/n) + s′`.

The scheme composes Lemma 6's quantum probe into `M1` with the `(t − 1)`-query scheme for `M2`
(padded with zeros to length `m″`), in place of the classical probe into `M2`.

**Formalization Note.** `s_Q(m, n, t) ≤ X + s_Q(m″, n, t − 1)` is stated for every `s′` that is
achievable at `(m″, n, t − 1)` (existence of a valid scheme), so no `sInf` is used. The side
condition `2n ≤ m1 ≤ m′/2` with `m′ = m + m1` is `2n ≤ m1 ≤ m`. The length `m″` is any
`m″ ≥ 2n⌈m/m1⌉` (the paper's `m″` is this length, which is at most `2n(m + m1)/m1`). `C` is an
absolute constant, chosen before `t` (the proof of Theorem 1 uses one `C` for all `t − 1`
applications); `log = log₂`; `n ≥ 1` (for `log(m1/n)`), `t ≥ 2` (for `t − 1 ≥ 1`). -/
theorem eq_3_recurrence : ∃ C : ℝ, ∀ m n t m₁ m'' s' : ℕ, 1 ≤ n → 2 ≤ t → 2 * n ≤ m₁ →
    m₁ ≤ m → 2 * n * ⌈(m : ℝ) / m₁⌉₊ ≤ m'' →
    (∃ S' : CompressionScheme m'' n s' (t - 1), S'.Valid) →
    ∃ s : ℕ, (s : ℝ) ≤ C * m₁ * Real.logb 2 ((m₁ : ℝ) / n) + s' ∧
      ∃ S : CompressionScheme m n s t, S.Valid := by sorry

end QRetrieval.Adaptive

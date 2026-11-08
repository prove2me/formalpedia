-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_trivial_scheme
-- name    : QRetrieval.Adaptive.trivial_scheme
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:52.690838+00:00
-- url     : https://prove2.me/theorems/44330790-931e-4a35-b16a-30c6ad41dc1c
-- title:
--   The obvious upper bound $s_Q(m,n,t)\le m$ (store $x$ itself)
-- statement:
--   For all natural numbers $m$, $n$ and $t\ge1$ there is a valid $(m,n,m,t)$-compression scheme; that is,
--
--   $$
--   s_Q(m,n,t)\ \le\ m .
--   $$
--
--   The scheme stores $y=x$ and reads $x_i$ with one query to $O_y$. This is the base case $t=1$ of the recursion in the proof of Theorem 1, and the bound used there when $m<64n$ or when the string left to compress is short.
--
--   Differences from the source:
--   - reading: the obvious upper bound s_Q(m, n, t) = m → a valid (m, n, m, t)-scheme exists (s_Q ≤ m); reason: the text calls it an upper bound; equality is false in general (for t ≥ 2 and m ≫ n, Theorem 1 gives less)
--   - encoding: for all m, n, t → 1 ≤ t; reason: 1/t in Theorem 1 presupposes t ≥ 1, and with t = 0 no circuit can read x when n ≥ 1
--   - encoding: Definition 2.1's circuit: unitaries controlled by the index register, at most t oracle gates O_y, a final measurement with outcome in {0,1} → one QueryAlg per index i with shared work register W and T ≤ t queries, controlledPhaseOracle, computational-basis measurement followed by out i; reason: the same class of circuits (an I-controlled unitary is one unitary per value of I; a two-outcome projective measurement is a basis change folded into U_T)
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §4, proof of Theorem 1 (unnumbered), p. 10

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_CompressionScheme

namespace QRetrieval.Adaptive

/-- **The obvious upper bound `s_Q(m, n, t) ≤ m` (store `x` itself).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §4, proof of Theorem 1 (unnumbered), p. 10: "We show that repeatedly applying
the above recurrence, together with the obvious upper bound `s_Q(m, n, t) = m` (in particular, for
the base case `t = 1`), yields the bound stated in Theorem 1."

For all `m`, all `n` and all `t ≥ 1` there is a valid `(m, n, m, t)`-compression scheme.

**Formalization Note.** "`s_Q(m, n, t) = m`" is read as the upper bound it is called in the text
(`s_Q ≤ m`: a valid scheme with `s = m` exists, storing `y = x`). `t ≥ 1` is needed because a
circuit with no oracle gate cannot read `x`. At `m = 0` the statement holds as well: `query` is a
function on `Fin 0`, so no query algorithm is needed and validity is vacuous. -/
theorem trivial_scheme : ∀ m n t : ℕ, 1 ≤ t →
    ∃ S : CompressionScheme m n m t, S.Valid := by sorry

end QRetrieval.Adaptive

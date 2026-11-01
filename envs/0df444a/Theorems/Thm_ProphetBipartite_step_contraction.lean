-- Prove2me | Theorems.Thm_ProphetBipartite_step_contraction
-- name    : ProphetBipartite.step_contraction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:49:57.384227+00:00
-- url     : https://prove2.me/theorems/3872ce25-1116-4d5e-a27b-3d154d31f32e
-- title:
--   Proof of Theorem 3.2, (19)–(21) — every round of Algorithm 1 contracts the error by $3/4$, so $t$ rounds by $(3/4)^t$
-- statement:
--   Let $M$, $Q$ be real $L\times R$ matrices with nonnegative entries such that every row sum and every column sum of $Q$ is at most $1$, and let $l\in\mathbb R^L$, $r\in\mathbb R^R$ be arbitrary. Let $\delta_L,\delta_R$ be the errors (18) at $(l,r)$, and $\hat\delta_L,\hat\delta_R$ the errors at the vectors produced by one round of Algorithm 1 ($l\leftarrow l-\frac12\delta_L$ if $\|\delta_L\|_1\ge\|\delta_R\|_1$, else $r\leftarrow r-\frac12\delta_R$). Then
--
--   $$
--   \|\hat\delta_L\|_1+\|\hat\delta_R\|_1\ \le\ \frac34\big(\|\delta_L\|_1+\|\delta_R\|_1\big).
--   $$
--
--   Consequently, if $(\delta_L(t),\delta_R(t))$ are the errors after $t$ rounds started from $(l,r)$, then
--
--   $$
--   \|\delta_L(t)\|_1+\|\delta_R(t)\|_1\ \le\ \Big(\frac34\Big)^t\big(\|\delta_L(0)\|_1+\|\delta_R(0)\|_1\big).
--   $$
--
--   This drives Algorithm 1 to a solution of (17).
--
--   Differences from the source:
--   - generalization: M, Q are the matrices of (10) → any real L × R matrices with nonnegative entries whose Q has row sums and column sums at most 1; reason: the proof uses only these properties of M, Q (Fact 3.2 and nonnegativity); the matrices of (10) are an instance by fact_3_2
--   - generalization: l, r the current iterates of Algorithm 1 → any real vectors l, r; reason: the contraction is a per-round statement; the iterates are an instance
--   - encoding: Algorithm 1 with the stopping test of line 9 → the iterates (algorithm1Step M Q)^[t] of one round, without a stopping test; reason: the proof of Theorem 3.2 itself lets the algorithm "continue indefinitely" (p.11); the stopping test changes no iterate before it fires
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, proof of Theorem 3.2, (18)–(21) and the display after (21), pp.10–11

import Mathlib
import Definitions.Def_ProphetBipartite_algorithm1Step

namespace ProphetBipartite

/-- **Proof of Theorem 3.2, (19)–(21): every round of Algorithm 1 contracts the error by `3/4`.**
Gravin & Wang, arXiv:1902.06243v1, pp.10–11: with the errors `δ_L`, `δ_R` of (18) and the update of
Algorithm 1, "the `L₁`-norm of the combined error decreases by a factor of `3/4` in every round and
after `t` steps the `L₁`-norm of the combined error `(δ_L(t), δ_R(t))` will be
`‖δ_L(t)‖₁ + ‖δ_R(t)‖₁ ≤ (3/4)^t (‖δ_L(0)‖₁ + ‖δ_R(0)‖₁)`". So

`‖δ̂_L‖₁ + ‖δ̂_R‖₁ ≤ (3/4)(‖δ_L‖₁ + ‖δ_R‖₁)`,

where `δ̂_L`, `δ̂_R` are the errors (18) at the updated vectors, and the `t`-round bound holds from
every starting point. Here `M`, `Q` are real matrices with
nonnegative entries (the input of Algorithm 1) and the row and column sums of `Q` are at most 1
(used on p.11 "since `∑_j Q_{i,j} ≤ 1`"; the column sums for an `r`-round), and `l`, `r` are any
real vectors.

**Formalization Note.** `error17 M Q l r` is `‖δ_L‖₁ + ‖δ_R‖₁`; `algorithm1Step` is one round
(lines 2–8), with the tie `‖δ_L‖₁ = ‖δ_R‖₁` updating `l`, as printed; `(algorithm1Step M Q)^[t]` is
`t` rounds, without the stopping rule. -/
theorem step_contraction {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) :
    error17 M Q (algorithm1Step M Q (l, r)).1 (algorithm1Step M Q (l, r)).2 ≤
        (3 / 4) * error17 M Q l r ∧
      ∀ t : ℕ, error17 M Q ((algorithm1Step M Q)^[t] (l, r)).1 ((algorithm1Step M Q)^[t] (l, r)).2 ≤
        (3 / 4) ^ t * error17 M Q l r := by sorry

end ProphetBipartite

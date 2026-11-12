-- Prove2me | Theorems.Thm_RiskBalancingMNL_eq_13_unique_root
-- name    : RiskBalancingMNL.eq_13_unique_root
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:44:39.25951+00:00
-- url     : https://prove2.me/theorems/7ed1c6f9-f054-4f4d-b6e1-9b6c556b0f45
-- title:
--   Eq. (13) — the left side increases in $q_0$ up to $1-\lambda$, with a unique root
-- statement:
--   Fix the MNL model with $n\ge1$ products and a risk weight $\lambda\in[0,\bar\lambda)$, and let
--   $$
--   F_\lambda(q_0)=\hat m(q_0)-\frac1{bq_0}+\frac{\lambda\,\hat m(q_0)}{2(1-q_0-\lambda)}
--   $$
--   be the left side of (13). Then
--
--   1. $F_\lambda$ is strictly increasing on $(0,1-\lambda)$;
--   2. $F_\lambda$ has exactly one root in $(0,1-\lambda)$;
--   3. that root lies in $(1-\bar\lambda,1-\lambda)$.
--
--   The root is the candidate no-purchase probability $q_0^*(\lambda)$ of Theorem 1, and (12) turns it into the unique candidate markup.
--
--   Differences from the source:
--   - reading: "the first-order condition has a unique q0 solution" → exactly one root in (0, 1 − λ); reason: the page restricts to "up to 1 − λ (see (10))"; on (1 − λ, 1) a second root can exist (A = 1, b = 1, λ = 1/4: near q₀ ≈ 0.947), which is not optimal
--   - reading: "monotonically increases in q0 up to 1 − λ" → strictly increasing on (0, 1 − λ); reason: the stronger reading; it is what uniqueness of the root uses
--   - generalization: a unique root → also the root lies in (1 − λ̄, 1 − λ); reason: an added conclusion: below 1 − λ̄ every term of F_λ is negative; it specializes to the page's claim
--   - reading: the printed last term m̂/(2[(1 − q₀)/λ − 1]) at λ = 0, where it is undefined → λm̂/(2(1 − q₀ − λ)), i.e. 0 at λ = 0; reason: its limit as λ → 0; for λ > 0 the two forms are equal on (0, 1 − λ)
--   - encoding: q₀ ∈ (0, 1 − λ) → open at 0; reason: m̂ is undefined at q₀ = 0
--   - encoding: n products → n ≥ 1; reason: needed for λ̄ > 0 and for (12)
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), eq. (13) and the following paragraph, p.11

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat

namespace RiskBalancingMNL

/-- **Eq. (13) and its unique root**, Li & Webster, *Optimizing Risk-balancing Return under
Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), p.11: "the left side of (13)
monotonically increases in `q₀` up to `1 − λ` … for any given `λ ∈ [0, λ̄)` … the first-order
condition has a unique `q₀` solution".

For `λ ∈ [0, λ̄)`, the left side of (13) is strictly increasing on `(0, 1 − λ)` and has exactly
one root there; that root lies in `(1 − λ̄, 1 − λ)`.

**Formalization Note** The left side of (13) is `foc` (last term `λm̂/(2(1 − q₀ − λ))`, equal to
the printed one for `λ > 0`, and its limit `0` at `λ = 0`). The interval is open at `0`, where
`m̂` is undefined. -/
theorem eq_13_unique_root {n : ℕ} [NeZero n] (P : Params n) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam : lam < lamBar P) :
    StrictMonoOn (foc P lam) (Set.Ioo 0 (1 - lam)) ∧
    (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧ foc P lam x = 0) ∧
    ∀ x ∈ Set.Ioo 0 (1 - lam), foc P lam x = 0 → 1 - lamBar P < x := by sorry

end RiskBalancingMNL

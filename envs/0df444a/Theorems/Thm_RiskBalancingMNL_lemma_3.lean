-- Prove2me | Theorems.Thm_RiskBalancingMNL_lemma_3
-- name    : RiskBalancingMNL.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:31.384118+00:00
-- url     : https://prove2.me/theorems/b534c1fa-a6d1-4c76-8b46-551441e35601
-- title:
--   Lemma 3 — $\tilde L(q_0)$ is unimodal (corrected: on the feasible range $1-\bar\lambda\le q_0<1-\lambda$)
-- statement:
--   Fix the MNL model with $n\ge1$ products and a risk weight $\lambda\in[0,\bar\lambda)$, and let $x\in(0,1-\lambda)$ be the root of (13). Then the univariate objective (14),
--   $$
--   \tilde L(q_0)=\hat m(q_0)^2(1-q_0)(1-q_0-\lambda),
--   $$
--   is strictly increasing on $[1-\bar\lambda,x]$ and strictly decreasing on $[x,1-\lambda)$.
--
--   So the root of (13) is the maximizer of $\tilde L$ over the no-purchase probabilities of feasible equal markups ($t\ge0$ corresponds to $q_0\ge1-\bar\lambda$).
--
--   Differences from the source:
--   - correction: L̃ unimodal on [0, 1 − λ) → on [1 − λ̄, 1 − λ), for λ ∈ [0, λ̄); reason: instance n = 1, a₁ = c₁ = 0, b = 1, λ = 0: L̃(q₀) = log²(q₀/(1 − q₀))(1 − q₀)², with L̃(0.01) ≈ 20.69, L̃(0.5) = 0, L̃(0.8) ≈ 0.077, so L̃ dips to 0 inside [0, 1) and is not unimodal; q₀ < 1 − λ̄ means m̂ < 0, which is infeasible (the constraint m ≥ 0 after (9))
--   - reading: "unimodal" (not defined in the paper) → strictly increasing on [1 − λ̄, x] and strictly decreasing on [x, 1 − λ), with x the root of (13); reason: the page's next sentence: "thus the unique solution of (13) is the optimal solution"
--   - encoding: n products → n ≥ 1; reason: needed for λ̄ > 0 and for (12)
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Lemma 3 and the preceding sentence, p.12; (14), p.11

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat

namespace RiskBalancingMNL

/-- **Lemma 3**, Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice Models*,
SSRN 3959428 (PDF of 2021-11-14), p.12, corrected to the feasible range `q₀ ≥ 1 − λ̄`: for
`λ ∈ [0, λ̄)`, with `x` the root of (13) in `(0, 1 − λ)`, `L̃` of (14) is strictly increasing on
`[1 − λ̄, x]` and strictly decreasing on `[x, 1 − λ)`.

**Formalization Note** "Unimodal" is not defined in the paper; it is read as "strictly increasing
up to a point and strictly decreasing after it", with the turning point the root of (13). The
printed range `[0, 1 − λ)` is false: there `q₀ < 1 − λ̄` means `m̂ < 0` and `L̃ → +∞` as
`q₀ → 0`. -/
theorem lemma_3 {n : ℕ} [NeZero n] (P : Params n) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam : lam < lamBar P) (x : ℝ) (hx : x ∈ Set.Ioo 0 (1 - lam)) (hfoc : foc P lam x = 0) :
    StrictMonoOn (LTilde P lam) (Set.Icc (1 - lamBar P) x) ∧
    StrictAntiOn (LTilde P lam) (Set.Ico x (1 - lam)) := by sorry

end RiskBalancingMNL

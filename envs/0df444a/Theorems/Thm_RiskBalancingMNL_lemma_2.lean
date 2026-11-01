-- Prove2me | Theorems.Thm_RiskBalancingMNL_lemma_2
-- name    : RiskBalancingMNL.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:38.424152+00:00
-- url     : https://prove2.me/theorems/3faac03b-487e-4c18-8151-6363288f7846
-- title:
--   Lemma 2 — the first-order condition (11) under equal markup (corrected: $t>0$)
-- statement:
--   Fix the MNL model with $n\ge1$ products, a risk weight $\lambda\in[0,1)$ and an equal markup $t>0$, and write $q_0=q_0(t,\dots,t)$, assuming $q_0\ne1-\lambda$. Then every partial derivative of $L_\lambda$ with respect to a single markup $m_j$ vanishes at $(t,\dots,t)$ if and only if
--   $$
--   t-\frac1{bq_0}+\frac{\lambda t}{2(1-q_0-\lambda)}=0 .\qquad (11)
--   $$
--   For $\lambda>0$ the last term equals the printed $t/(2[(1-q_0)/\lambda-1])$.
--
--   The equation reduces the $n$ first-order conditions to one equation in $t$; the last term is the effect of risk aversion.
--
--   **Formalization Note** The partial derivative in coordinate $j$ is the derivative of $s\mapsto L_\lambda(t,\dots,s,\dots,t)$ ($s$ in position $j$) at $s=t$.
--
--   Differences from the source:
--   - correction: the equal-markup first-order condition reduces to (11), for every equal markup → for equal markups t > 0; reason: at t = 0 the gradient of L vanishes while (11) reads −1/(bq₀) = 0; instance n = 1, a₁ = c₁ = 0, b = 1, λ = 0, t = 0: q₀ = 1/2, every partial derivative is 0, and the left side of (11) is −2
--   - reading: the last term m/(2[(1 − q₀)/λ − 1]) at λ = 0, where it is undefined → λm/(2(1 − q₀ − λ)), i.e. 0 at λ = 0; reason: the limit of the printed term as λ → 0; it gives the risk-neutral condition m = 1/(bq₀)
--   - encoding: m/(2[(1 − q₀)/λ − 1]) for λ > 0 → λm/(2(1 − q₀ − λ)); reason: equal for λ > 0 and q₀ ≠ 1 − λ
--   - encoding: (11) wherever it is defined → hypothesis q₀ ≠ 1 − λ; reason: at q₀ = 1 − λ the printed denominator is 0, so this excludes only undefined cases
--   - encoding: the first-order condition of (6) in the shares q → vanishing partial derivatives of L in each markup mⱼ; reason: markups and shares are related by a smooth bijection (p.9–10), so the two first-order conditions are equivalent
--   - encoding: n products → n ≥ 1; reason: with no product q₀ = 1 and the gradient condition is empty
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Lemma 2 and eq. (11), p.11

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params

namespace RiskBalancingMNL

/-- **Lemma 2**, Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice Models*,
SSRN 3959428 (PDF of 2021-11-14), p.11: under equal markup the first-order condition reduces to
(11), `m − 1/(bq₀) + m / (2[(1 − q₀)/λ − 1]) = 0`.

Stated as: for `λ ∈ [0, 1)` and an equal markup `t > 0` with `q₀ = q₀(t) ≠ 1 − λ`, every partial
derivative of `L` at `(t, …, t)` vanishes iff `t − 1/(bq₀) + λt / (2(1 − q₀ − λ)) = 0`.

**Formalization Note** The partial derivative in coordinate `j` is the derivative of
`s ↦ L(t, …, s, …, t)` (`Function.update`) at `s = t`. The last term of (11) is written
`λt/(2(1 − q₀ − λ))`, which equals the printed one for `λ > 0`, and is its limit `0` at `λ = 0`.
`t > 0` is needed: at `t = 0` the gradient vanishes while (11) reads `−1/(bq₀) = 0`.
`q₀ ≠ 1 − λ` keeps the denominators of (11) nonzero; `n ≥ 1` (`NeZero n`), as in the model. -/
theorem lemma_2 {n : ℕ} [NeZero n] (P : Params n) (lam t : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (ht : 0 < t) (hq : noPurchase P (constM t) ≠ 1 - lam) :
    (∀ j : Fin n,
      HasDerivAt (fun s : ℝ => objective P lam (Function.update (constM t) j s)) 0 t) ↔
    t - 1 / (P.b * noPurchase P (constM t)) +
      lam * t / (2 * (1 - noPurchase P (constM t) - lam)) = 0 := by sorry

end RiskBalancingMNL

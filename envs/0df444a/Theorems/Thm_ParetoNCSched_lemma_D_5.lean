-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_D_5
-- name    : ParetoNCSched.lemma_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:44.759562+00:00
-- url     : https://prove2.me/theorems/ad1c62bb-917d-46de-860d-ecbec3f49b6c
-- title:
--   Lemma D.5 — the profile $x^*$ attains $\int_0^1(1-x^*)^2=c(R)-1$
-- statement:
--   Let $R>2$, with $\beta,\gamma,\alpha,K$ of (14), $W,\tilde w$ of (15), the profile $x^*$ and $\lambda(R)$ of (16). Then:
--
--   1. (a) $W$ is $C^1$ and strictly increasing on $[0,\tilde\xi]$, with $W(0)=0$, $0<\tilde w<1$ and
--   $$W'(\xi)=\frac{2\,(1-W(\xi))\,(1-(1+R)\xi)}{(R+2)(1-\xi)(\xi+\beta)}\qquad(\xi\in[0,\tilde\xi]);$$
--   consequently $x^*$ is well defined ($x^*(w)\in[0,\tilde\xi]$ and $W(x^*(w))=w$ for $w\in[0,\tilde w)$), non-decreasing and right-continuous on $[0,1]$, with $x^*<\tilde\xi$ on $[0,\tilde w)$;
--   2. (b) $x^*$ satisfies (10) with equality: $\Gamma_{x^*}=0$ on $[0,\tilde w)$, and $\int_0^{\tilde w}q(x^*(v))\,dv+(1-\tilde w)\,h(\tilde\xi)=0$;
--   3. (c) $\displaystyle\int_0^1\big(1-x^*(w)\big)^2dw=\lambda(R)=c(R)-1$.
--
--   Together with Theorem D.4 this gives the consistency bound $c(R)$.
--
--   Differences from the source:
--   - encoding: W′(ξ) and "C¹" on [0, ξ̃] → derivative within [0, ξ̃] (one-sided at the endpoints) and `ContDiffOn ℝ 1` on [0, ξ̃]; reason: the standard meaning on a closed interval
--   - encoding: x* = W⁻¹ on [0, w̃) → the generalized inverse inf{ξ ∈ [0, ξ̃] : W(ξ) ≥ w}, and "well defined" as x*(w) ∈ [0, ξ̃], W(x*(w)) = w for w ∈ [0, w̃); reason: equal to W⁻¹ there because W is a continuous increasing bijection [0, ξ̃] → [0, w̃]
--   - encoding: x* non-decreasing and right-continuous → monotone on [0, 1] and right-continuous at every w ∈ [0, 1); reason: x* is a function on [0, 1]
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.5, Eqs. (14)–(16), p.28

import Mathlib
import Definitions.Def_ParetoNCSched_xStar
import Definitions.Def_ParetoNCSched_lamR
import Definitions.Def_ParetoNCSched_cR
import Definitions.Def_ParetoNCSched_hFun
import Definitions.Def_ParetoNCSched_qFun
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma D.5 (The profile).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Lemma D.5, p.28: "With the definitions above, it holds
that (a) W is C¹ and strictly increasing on [0, ξ̃], with W(0) = 0, 0 < w̃ < 1 and
W′(ξ) = 2(1 − W(ξ))(1 − (1 + R)ξ) / ((R + 2)(1 − ξ)(ξ + β)). Consequently x* is well defined,
non-decreasing and right-continuous, with x* < ξ̃ on [0, w̃). (b) x* satisfies (10) with equality:
Γ_{x*} = 0 on [0, w̃), and ∫₀^w̃ q(x*(v)) dv + (1 − w̃) h(ξ̃) = 0. (c) ∫₀¹ (1 − x*(w))² dw = λ(R) =
c(R) − 1." The definitions are (14)–(16), p.28, under "Throughout, R > 2" (p.20).

**Formalization Note.** W′ is the derivative within `[0, ξ̃]` (one-sided at the endpoints). "x* is
well defined" is: for `w ∈ [0, w̃)`, `x*(w) ∈ [0, ξ̃]` and `W(x*(w)) = w`. Monotonicity and right
continuity of `x*` are on `[0, 1]`. -/
theorem lemma_D_5 (R : ℝ) (hR : 2 < R) :
    -- (a)
    (ContDiffOn ℝ 1 (Wp R) (Icc 0 (xiT R)) ∧ StrictMonoOn (Wp R) (Icc 0 (xiT R)) ∧
      Wp R 0 = 0 ∧ 0 < wT R ∧ wT R < 1 ∧
      (∀ ξ ∈ Icc 0 (xiT R), HasDerivWithinAt (Wp R)
        (2 * (1 - Wp R ξ) * (1 - (1 + R) * ξ) / ((R + 2) * (1 - ξ) * (ξ + betR R)))
        (Icc 0 (xiT R)) ξ) ∧
      (∀ w ∈ Ico 0 (wT R), xStar R w ∈ Icc 0 (xiT R) ∧ Wp R (xStar R w) = w) ∧
      MonotoneOn (xStar R) (Icc 0 1) ∧
      (∀ w ∈ Ico (0 : ℝ) 1, ContinuousWithinAt (xStar R) (Ici w) w) ∧
      (∀ w ∈ Ico 0 (wT R), xStar R w < xiT R)) ∧
    -- (b)
    ((∀ w ∈ Ico 0 (wT R),
        (∫ v in (0 : ℝ)..w, qFun R (xStar R v)) + (1 - w) * hFun R (xStar R w) = 0) ∧
      (∫ v in (0 : ℝ)..wT R, qFun R (xStar R v)) + (1 - wT R) * hFun R (xiT R) = 0) ∧
    -- (c)
    ((∫ w in (0 : ℝ)..1, (1 - xStar R w) ^ 2) = lamR R ∧ lamR R = cR R - 1) := by sorry

end ParetoNCSched

-- Prove2me | Theorems.Thm_ParetoNCSched_theorem_D_4
-- name    : ParetoNCSched.theorem_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:22:35.361785+00:00
-- url     : https://prove2.me/theorems/41363cd7-9687-44ca-925c-b703c5236dd2
-- title:
--   Theorem D.4 — comparison with a target $x$
-- statement:
--   Let $R>2$ and let $h,q,\tilde\xi$ be as in (9): $h(\xi)=\xi-\frac{1+R}{2}\xi^2$, $q(\xi)=\frac{(1-\xi)^2-(R-1)}{2}$, $\tilde\xi=\frac1{1+R}$. Let $x:[0,1]\to[0,1]$ be non-decreasing and right-continuous, and let $\tilde w\in(0,1]$ be such that $x(w)<\tilde\xi$ for $w<\tilde w$ and $x(w)=1$ for $w\ge\tilde w$. For $w\in[0,\tilde w)$ let
--   $$\Gamma_x(w)=\int_0^w q\big(x(v)\big)\,dv+(1-w)\,h\big(x(w)\big),$$
--   and suppose that
--   $$\Gamma_x(w)\le0\ \text{ for all } w\in[0,\tilde w),\qquad \int_0^{\tilde w}q\big(x(v)\big)\,dv+(1-\tilde w)\,h(\tilde\xi)\le0. \tag{10}$$
--   Then, for every instance $p\in(0,\infty)^n$ and every correct predicted order $\sigma$,
--   $$\mathrm{MRC}_R(p,\sigma)\le\Big(1+\int_0^1\big(1-x(w)\big)^2dw\Big)\,\mathrm{OPT}(p).$$
--
--   Any admissible target certifies a consistency bound; Lemma D.5 supplies the target that gives $c(R)$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: x : [0, 1] → [0, 1] non-decreasing and right-continuous → x : ℝ → ℝ with values in [0, 1] on [0, 1], monotone on [0, 1], right-continuous at every w ∈ [0, 1); reason: values outside [0, 1] never enter the statement; right-continuity at w = 1 is vacuous on [0, 1]
--   - encoding: integrals ∫₀^w, ∫₀^w̃, ∫₀¹ → interval integrals; reason: the integrands are bounded and monotone or a continuous function of a monotone one on [0, 1], hence integrable
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem D.4, Eqs. (9)–(10), p.24

import Mathlib
import Definitions.Def_ParetoNCSched_mrcCost
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_IsCorrect
import Definitions.Def_ParetoNCSched_hFun
import Definitions.Def_ParetoNCSched_qFun
import Definitions.Def_ParetoNCSched_xiT
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Theorem D.4 (Comparison with a target).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, Theorem D.4, p.24: "Let R > 2. Let
x : [0, 1] → [0, 1] be non-decreasing and right-continuous, and let w̃ ∈ (0, 1] be such that
x(w) < ξ̃ for w < w̃ and x(w) = 1 for w ≥ w̃. For w ∈ [0, w̃) let
Γ_x(w) = ∫₀^w q(x(v)) dv + (1 − w) h(x(w)), and suppose that Γ_x(w) ≤ 0 for all w ∈ [0, w̃), and
∫₀^w̃ q(x(v)) dv + (1 − w̃) h(ξ̃) ≤ 0. (10) Then, on every instance with a correct predicted order,
MRC_R ≤ (1 + ∫₀¹ (1 − x(w))² dw) OPT." `h`, `q`, `ξ̃` are those of (9), p.24.

**Formalization Note.** `x : ℝ → ℝ` is constrained on `[0, 1]` only: values in `[0, 1]`, monotone on
`[0, 1]`, right-continuous at every `w ∈ [0, 1)`. Integrals are interval integrals
(`q ∘ x` and `(1 − x)²` are bounded and monotone-composed, hence integrable on `[0, 1]`). -/
theorem theorem_D_4 (R : ℝ) (hR : 2 < R) (x : ℝ → ℝ) (wt : ℝ)
    (hx_range : ∀ w ∈ Icc (0 : ℝ) 1, x w ∈ Icc (0 : ℝ) 1)
    (hx_mono : MonotoneOn x (Icc 0 1))
    (hx_rc : ∀ w ∈ Ico (0 : ℝ) 1, ContinuousWithinAt x (Ici w) w)
    (hwt : wt ∈ Ioc (0 : ℝ) 1)
    (hx_below : ∀ w ∈ Ico 0 wt, x w < xiT R)
    (hx_one : ∀ w ∈ Icc wt 1, x w = 1)
    (h10a : ∀ w ∈ Ico 0 wt, (∫ v in (0 : ℝ)..w, qFun R (x v)) + (1 - w) * hFun R (x w) ≤ 0)
    (h10b : (∫ v in (0 : ℝ)..wt, qFun R (x v)) + (1 - wt) * hFun R (xiT R) ≤ 0) :
    ∀ {n : ℕ} (p : Fin n → ℝ), (∀ j, 0 < p j) → ∀ σ : Equiv.Perm (Fin n), IsCorrect p σ →
      mrcCost R p σ ≤ ENNReal.ofReal (1 + ∫ w in (0 : ℝ)..1, (1 - x w) ^ 2) * OPT p := by sorry

end ParetoNCSched

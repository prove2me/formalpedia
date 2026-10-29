-- Prove2me | Theorems.Thm_PeskirShiryaev_SharpInequalities_brownian_log
-- name    : PeskirShiryaev.SharpInequalities.brownian_log
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:01.854595+00:00
-- url     : https://prove2.me/theorems/36f1d5e6-a8cd-4dde-ae0c-2cde8a3760f5
-- title:
--   Theorem 19.1 — Sharp Brownian L log L
-- statement:
--   Let $B$ be standard real Brownian motion started at zero under $P$. Fix $c>1$. Put $X_t=|B_t|$ and $G(y)=y\log y$, with $G(0)=0$. For every stopping time $\tau$ of $B$ satisfying $\mathbb E\tau^r<\infty$ for some $r>1/2$,
--
--   $$\mathbb E\max_{0\le t\le\tau}X_t\le \frac{c^2}{e(c-1)}+c\,\mathbb E G(X_\tau).$$
--
--   The inequality is sharp: equality is attained by $\sigma_*$ from the Brownian stopping definitions, with this process $X$. This time is itself admissible and its cost expectation is finite.
--
--   This zero-start bound is a milestone toward the corresponding initial-value-dependent inequality.
--
--   **Formalization Note** Brownian motion is represented by its measurable continuous version and stopping times use its natural filtration. Both sides are extended expectations; no finite-cost assumption is imposed on the arbitrary stopping time. The explicit attaining time and its admissibility are conclusions, not assumptions.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 274 (PDF p. 292), Theorem 19.1, Eqs. (19.2.1)–(19.2.2)

import Definitions.Def_PeskirShiryaev_SharpInequalities_brownianStopping
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace PeskirShiryaev.SharpInequalities

/-- BrownianData means a standard real Brownian motion B with measurable evaluations,
continuous paths and B₀=0. Admissible means a stopping time of the natural filtration,
a.s. finite, with E[τ^r]<∞ for some real r>1/2. maximumExpectation is
E[sup_{0≤t≤τ}|B_t+x|], formed using nonnegative extended integrals.
costExpectation is E[G(Y)+1/e]-1/e in EReal, where G(y)=y log y for plain,
and G(y)=y max(log y,0) for plus; G(0)=0. Thus infinite expectations stay infinite.
For plain, boundConstant is c²/[e(c-1)] for x≤v=c/[e(c-1)] and
cx log(c/[x(c-1)]) above v. For plus it is u=1+1/[exp(c)(c-1)] for x≤u,
x+(1-x)log(x-1)-(c+log(c-1))(x-1) for u<x≤s=c/(c-1), and
cx log(c/[x(c-1)]) for x>s. All overlaps agree.
optimalTime is inf{t>0 : S_t≥v, |B_t+x|=α S_t} for plain, and
inf{t>0 : S_t≥u, |B_t+x|=max(1,α S_t)} for plus, where α=(c-1)/c
and S_t=sup_{0≤r≤t}|B_r+x|. Empty hitting sets have infimum infinity.
The equality clause includes admissibility and finite cost expectation. -/
theorem brownian_log {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : BrownianData Ω P)
    (c : ℝ) (hc : 1 < c) :
    (∀ τ : Ω → ℝ≥0∞, Admissible P D τ →
      maximumExpectation P D.B 0 τ ≤ ((c ^ 2 / (Real.exp 1 * (c - 1)) : ℝ) : EReal) +
        (c : EReal) * costExpectation P .plain (stoppedAbsolute D.B 0 τ)) ∧
    Admissible P D (optimalTime D.B .plain 0 c) ∧
    costExpectation P .plain (stoppedAbsolute D.B 0 (optimalTime D.B .plain 0 c)) < ⊤ ∧
    maximumExpectation P D.B 0 (optimalTime D.B .plain 0 c) =
      ((c ^ 2 / (Real.exp 1 * (c - 1)) : ℝ) : EReal) + (c : EReal) *
        costExpectation P .plain (stoppedAbsolute D.B 0 (optimalTime D.B .plain 0 c)) := by sorry

end PeskirShiryaev.SharpInequalities

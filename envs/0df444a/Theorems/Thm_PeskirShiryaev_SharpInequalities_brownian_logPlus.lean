-- Prove2me | Theorems.Thm_PeskirShiryaev_SharpInequalities_brownian_logPlus
-- name    : PeskirShiryaev.SharpInequalities.brownian_logPlus
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:09.324517+00:00
-- url     : https://prove2.me/theorems/2d44c83a-9c5e-4691-8edc-96ba5090c0fc
-- title:
--   Theorem 19.3 — Sharp Brownian L log+ L
-- statement:
--   Let $B$ be standard real Brownian motion started at zero under $P$. Fix $c>1$. Put $X_t=|B_t|$ and $G(y)=y\log^+y=y\max(\log y,0)$, with $G(0)=0$. For every stopping time $\tau$ of $B$ satisfying $\mathbb E\tau^r<\infty$ for some $r>1/2$,
--
--   $$\mathbb E\max_{0\le t\le\tau}X_t\le 1+\frac{1}{e^c(c-1)}+c\,\mathbb E G(X_\tau).$$
--
--   The inequality is sharp: equality is attained by $\tau_*$ from the Brownian stopping definitions, with this process $X$. This time is itself admissible and its cost expectation is finite.
--
--   This zero-start bound is a milestone toward the corresponding initial-value-dependent inequality.
--
--   **Formalization Note** Brownian motion is represented by its measurable continuous version and stopping times use its natural filtration. Both sides are extended expectations; no finite-cost assumption is imposed on the arbitrary stopping time. The explicit attaining time and its admissibility are conclusions, not assumptions.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 279 (PDF p. 297), Theorem 19.3, Eqs. (19.2.29)–(19.2.30)

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
theorem brownian_logPlus {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : BrownianData Ω P)
    (c : ℝ) (hc : 1 < c) :
    (∀ τ : Ω → ℝ≥0∞, Admissible P D τ →
      maximumExpectation P D.B 0 τ ≤ ((1 + 1 / (Real.exp c * (c - 1)) : ℝ) : EReal) +
        (c : EReal) * costExpectation P .plus (stoppedAbsolute D.B 0 τ)) ∧
    Admissible P D (optimalTime D.B .plus 0 c) ∧
    costExpectation P .plus (stoppedAbsolute D.B 0 (optimalTime D.B .plus 0 c)) < ⊤ ∧
    maximumExpectation P D.B 0 (optimalTime D.B .plus 0 c) =
      ((1 + 1 / (Real.exp c * (c - 1)) : ℝ) : EReal) + (c : EReal) *
        costExpectation P .plus (stoppedAbsolute D.B 0 (optimalTime D.B .plus 0 c)) := by sorry

end PeskirShiryaev.SharpInequalities

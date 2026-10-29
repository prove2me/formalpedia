-- Prove2me | Theorems.Thm_PeskirShiryaev_SharpInequalities_submartingale_logarithmic_maximal
-- name    : PeskirShiryaev.SharpInequalities.submartingale_logarithmic_maximal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:05.734994+00:00
-- url     : https://prove2.me/theorems/ca240709-4d58-4d81-a249-119826bee756
-- title:
--   Corollary 19.6 — Sharp logarithmic maximal inequalities for submartingales
-- statement:
--   Let $X=(X_t)_{t\ge0}$ be a nonnegative càdlàg uniformly integrable submartingale on a filtered probability space, started at $x\ge0$. Its measurable almost sure limit $X_\infty$ exists as $t\to\infty$. For every $c>1$, and for either $G(y)=y\log y$ or $G(y)=y\log^+ y$ with $G(0)=0$,
--   $$\mathbb E\sup_{t>0}X_t\le W_G(x;c)+c\,\mathbb E G(X_\infty).$$
--
--   Write $\alpha=(c-1)/c$, $v_*=c/[e(c-1)]$, $u_*=1+1/[e^c(c-1)]$, and $s_*=c/(c-1)$. The constants are
--   $$
--   W_{\log}(x;c)=\begin{cases}c^2/[e(c-1)]&0\le x\le v_*,\\cx\log\!\frac{c}{x(c-1)}&x>v_*,\end{cases}
--   $$
--   and
--   $$
--   W_+(x;c)=\begin{cases}u_*&0\le x\le u_*,\\x+(1-x)\log(x-1)-(c+\log(c-1))(x-1)&u_*<x\le s_*,\\cx\log\!\frac{c}{x(c-1)}&x>s_* .\end{cases}
--   $$
--   Adjacent branches agree at their endpoints.
--
--   The inequality is sharp for each fixed $x\ge0$ and $c>1$: in each cost case there is an example in this submartingale class with finite cost expectation attaining equality. This is the chapter's extension of the Brownian bounds to general nonnegative submartingales.
--
--   **Formalization Note** The existence of the terminal limit is a conclusion. Infinite expectations retain their extended-real meaning. Sharpness is an existential finite equality example on a canonical path carrier with its own probability measure and filtration, not on the arbitrary space of the given process. No embedding theorem or moment condition is added to the hypotheses of the submartingale result.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 282 (PDF p. 300), Corollary 19.6, Eq. (19.2.46); constants Eqs. (19.2.28), (19.2.45)

import Definitions.Def_PeskirShiryaev_SharpInequalities_submartingaleSetting
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace PeskirShiryaev.SharpInequalities

/-- IsUICadlagSubmartingale means Mathlib's submartingale and uniform L¹ integrability,
with X₀=x, X_t≥0 for every t, right-continuity at every t, and a finite left limit
at every t>0, all on a single full-measure set.
fullMaximumExpectation is the nonnegative extended integral of sup_{t>0} max(X_t,0).
costExpectation is the nonnegative extended integral of max(G(Y)+1/e,0), minus
finite 1/e in EReal. For plain G(y)=y log y; for plus G(y)=y max(log y,0).
For nonnegative Y the integrand's outer max is inactive, since G(y)≥-1/e.
For plain, boundConstant is c²/[e(c-1)] for x≤v=c/[e(c-1)] and
cx log(c/[x(c-1)]) above v. For plus it is u=1+1/[exp(c)(c-1)] for x≤u,
x+(1-x)log(x-1)-(c+log(c-1))(x-1) for u<x≤s=c/(c-1), and
cx log(c/[x(c-1)]) for x>s. Adjacent formulas agree for c>1.
The second conjunct writes out a finite equality example explicitly, on the
canonical function carrier with its PRODUCT measurable space, with its own
probability measure, filtration, process and a.e.-measurable terminal limit. -/
theorem submartingale_logarithmic_maximal {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hX : IsUICadlagSubmartingale P ℱ X x) (k : LogCost) (c : ℝ) (hc : 1 < c) :
    (∃ Y : Ω → ℝ, AEMeasurable Y P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t => X t ω) atTop (𝓝 (Y ω))) ∧
      fullMaximumExpectation P X ≤ (boundConstant k x c : EReal) +
        (c : EReal) * costExpectation P k Y) ∧
    (∃ (Q : Measure (ℝ≥0 → ℝ))
      (𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Z : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (L : (ℝ≥0 → ℝ) → ℝ),
      IsProbabilityMeasure Q ∧ IsUICadlagSubmartingale Q 𝒢 Z x ∧
      AEMeasurable L Q ∧ (∀ᵐ ω ∂Q, Tendsto (fun t => Z t ω) atTop (𝓝 (L ω))) ∧
      costExpectation Q k L < ⊤ ∧
      fullMaximumExpectation Q Z = (boundConstant k x c : EReal) +
        (c : EReal) * costExpectation Q k L) := by sorry

end PeskirShiryaev.SharpInequalities

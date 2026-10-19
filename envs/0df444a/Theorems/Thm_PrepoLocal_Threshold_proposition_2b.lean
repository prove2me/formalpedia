-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_proposition_2b
-- name    : PrepoLocal.Threshold.proposition_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:59.867623+00:00
-- url     : https://prove2.me/theorems/35cde06f-26cd-4a55-bd7a-13fc540050e1
-- title:
--   Proposition 2(b), p. 10 (corrected reading) — if b ≥ b̄, x̄∗ = min{(x₊)⁺, b} is optimal for C on [0, b], and = (x₊)⁺ when max{αmin{d,q} − r} − γT̲ ≥ 0
-- statement:
--   In the single-cycle prepo model (parameters $0<\alpha<1$, $i\ge0$, $v>1$, $b\ge0$, $\gamma\ge0$; integrable, nonnegative $D,Q,R,T$ with $T$ independent of $(D,Q,R)$), let $C$ be the expected cycle cost of problem $\Pi$, $C_a$ the auxiliary cost, $\beta^*=i\mu_T/(v-1)$, and $x_+=\bar F^{-1}_{D-Q}(\beta^*)$ a net-demand fractile as in eq. (4). Suppose the budget is at least the threshold
--   $$
--   \bar b=\max\{\alpha\min\{d,q\}-r:(d,q,r)\in\Omega\}-\gamma\underline T+(x_+)^+ \tag{5}
--   $$
--   in the form: $\alpha\min\{D,Q\}-R\le M$ almost surely, $T\ge T_{lo}$ almost surely, and $M-\gamma T_{lo}+(x_+)^+\le b$. Then:
--   1. $\bar x^*=\min\{(x_+)^+,b\}$ is an optimal prepo stock for $\Pi$, i.e. it minimizes $C$ over $0\le x\le b$ (this is $x^*=\bar x^*$);
--   2. $\bar x^*$ also minimizes the auxiliary cost $C_a$ over $0\le x\le b$;
--   3. if moreover $M-\gamma T_{lo}\ge0$, then $\bar x^*=(x_+)^+$, so that
--   $$
--   x^*=\bar x^*=\bigl(\bar F^{-1}_{D-Q}(\beta^*)\bigr)^+ .
--   $$
--
--   Above the threshold budget, the HO's prepositioning problem is a newsvendor problem on the net demand $D-Q$, and the newsvendor heuristic of eq. (4) is exact.
--
--   **Formalization Note** *Correction.* The paper prints "If $b\ge\bar b$, then $x^*=\bar x^*=(\bar F^{-1}_{D-Q}(\beta^*))^+$". The last equality needs $b\ge(x_+)^+$, which follows from $b\ge\bar b$ only when $\max\{\alpha\min\{d,q\}-r\}-\gamma\underline T\ge0$. Counterexample to the printed version: $\gamma=0$ and $R=\alpha D+1$ almost surely, so the maximum is $-1$ and $\bar b=(x_+)^+-1$; with $x_+>1/2$ and $b=(x_+)^+-1/2$ we have $b\ge\bar b$, but $(x_+)^+>b$ is infeasible and the optimum is $b$. Clause 3 is the printed equality under this extra condition, and clauses 1–2 hold under $b\ge\bar b$ alone. *Other conventions.* $b\ge\bar b$ is encoded through almost-sure bounds $M$, $T_{lo}$, equivalently (take $M$ the maximum in (5) and $T_{lo}=\underline T$; conversely $\bar b\le M-\gamma T_{lo}+(x_+)^+$ since $\gamma\ge0$); the condition $M-\gamma T_{lo}\ge0$ is implied by the page's $\max\{\alpha\min\{d,q\}-r\}-\gamma\underline T\ge0$ with that choice. "$x^*=\bar x^*$" is read as "$\bar x^*$ is a minimizer" (`IsMinOn`) because $C$ is convex but not strictly convex. The domain is $[0,b]$. The paper's densities are not assumed.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 10, Proposition 2(b), with eq. (4), p. 9, and eq. (5), p. 10

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- Proposition 2(b), p. 10, corrected reading: if `b ≥ b̄` of (5) (encoded through a.s.
bounds `M` on `α min{D,Q} − R` and `Tlo` on `T`), then `x̄∗ = min{(x₊)⁺, b}` is an optimal
prepo stock for Π on `[0, b]` and for the auxiliary model; and `x̄∗ = (x₊)⁺` whenever
`M − γ Tlo ≥ 0` (the printed "`= (F̄⁻¹_{D−Q}(β∗))⁺`" needs this extra condition). -/
theorem proposition_2b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b) :
    IsMinOn (C P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) ∧
      IsMinOn (Ca P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) ∧
      (0 ≤ M - P.gam * Tlo → min (max xplus 0) P.b = max xplus 0) := by sorry

end PrepoLocal.Threshold

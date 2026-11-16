-- Prove2me | Theorems.Thm_UnionVolEst_Supplement_theorem_32
-- name    : UnionVolEst.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:11:01.253289+00:00
-- url     : https://prove2.me/theorems/201d6166-300a-4409-b683-e4551c6b6069
-- title:
--   Theorem 32 — every $t\ge1+\lfloor n/2\rfloor+\lceil(n\log(32R/d)+\log(1/(\eta^2\beta)))/(2\gamma_{HR})\rceil$ gives $\pi(\mathrm{Bad}_{t,\eta})\le\beta$ and $D_t(\mathrm{Bad}_{t,\eta})\le2\beta$
-- statement:
--   This is the general walk-length bound for Hit-and-Run in terms of its spectral gap.
--
--   Let $n\ge2$ and let $K\subseteq\mathbb R^n$ be a convex body contained in a Euclidean ball of radius $R$. Let $x_0$ be an interior point of $K$ with $d=\mathrm{dist}(x_0,\partial K)$, let $D_t$ be the law of Hit-and-Run after $t$ steps started at $x_0$, let $\pi$ be the uniform distribution on $K$, and let $\gamma_{HR}$ be the spectral gap of Hit-and-Run on $K$. Let $0<\eta,\beta<1$. Then every integer $t$ with
--   $$
--   t\;\ge\;1+\lfloor n/2\rfloor+\left\lceil\frac{n\log(32R/d)+\log\big(1/(\eta^2\beta)\big)}{2\gamma_{HR}}\right\rceil
--   $$
--   satisfies
--   $$
--   \pi(\mathrm{Bad}_{t,\eta})\le\beta,\qquad D_t(\mathrm{Bad}_{t,\eta})\le2\beta,
--   $$
--   where $\mathrm{Bad}_{t,\eta}=\{x\in K:|dD_t/d\pi(x)-1|>\eta\}$.
--
--   Combined with a lower bound on $\gamma_{HR}$ (Lemma 33), this gives Theorem 21.
--
--   **Formalization Note** $\gamma_{HR}$ takes values in $[0,\infty]$. The ceiling condition is stated without division by a possibly zero real: $t\ge1+\lfloor n/2\rfloor$ and $\frac{A}{2\gamma_{HR}}\le t-1-\lfloor n/2\rfloor$ in $[0,\infty]$, where $A$ is the numerator. The case $n\ge2$ is the standing assumption of Appendix C.1, since in dimension one a single step is exactly uniform.
--
--   Differences from the source:
--   - encoding: every integer t ≥ 1 + ⌊n/2⌋ + ⌈(n log(32R/d) + log(1/(η²β)))/(2γ_HR)⌉ → 1 + ⌊n/2⌋ ≤ t and ofReal(n log(32R/d) + log(1/(η²β))) / (2γ_HR) ≤ t − 1 − ⌊n/2⌋ in ℝ≥0∞; reason: for 0 < γ_HR < ∞ an integer is at least ⌈x⌉ iff it is at least x; γ_HR = 0 makes the bound +∞ (the numerator is positive, since d ≤ R), γ_HR = ∞ makes it 0, so no junk division enters
--   - generalization: the bounds π(Bad_{t,η}) ≤ β and D_t(Bad_{t,η}) ≤ 2β → IsAlmostLinftyClose η β D_t π, which also asserts D_t ≪ π; reason: the page states that ρ_t = dD_t/dπ exists for t ≥ 1 (p.43); the two bounds are the remaining conjuncts
--   - generalization: the App. C setup: K contains a Euclidean ball of radius r → no inball hypothesis (K has nonempty interior because x₀ ∈ interior K); reason: r does not appear in Theorem 32; every body of the setup satisfies the Lean hypotheses
--   - encoding: γ_HR, the spectral gap of Hit and Run; d = dist(x₀, ∂K); convex body; log → the published HitRunGaps.Spectral.hitRunGap K (ℝ≥0∞-valued Rayleigh infimum of the Hit-and-Run Dirichlet form over nonzero mean-zero f ∈ L²(π)); Metric.infDist x₀ Kᶜ; compact convex set; natural logarithm; reason: same objects
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Theorem 32, App. C.1, p.44 (PDF p.46), Eq. (19)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_Supplement_hitRunLaw
import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory ProbabilityTheory

namespace UnionVolEst.Supplement

/-- Theorem 32 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of
Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), App. C.1, printed p.44,
PDF p.46): let `n ≥ 2`, let `K ⊆ ℝⁿ` be a convex body contained in a ball of radius `R`, let `x₀`
be an interior point at distance `d = dist(x₀, ∂K)` from the boundary, let `γ_HR` be the spectral
gap of Hit-and-Run on `K`, and let `0 < η, β < 1`. Then every integer
`t ≥ 1 + ⌊n/2⌋ + ⌈(n log(32R/d) + log(1/(η²β)))/(2γ_HR)⌉` (19) satisfies
`π(Bad_{t,η}) ≤ β` and `D_t(Bad_{t,η}) ≤ 2β`.

**Formalization Note** `γ_HR` is the published `HitRunGaps.Spectral.hitRunGap K` (in `ℝ≥0∞`):
the infimum over nonzero mean-zero `f ∈ L²(π)` of the Hit-and-Run Dirichlet form over `‖f‖²`.
With `k = t − 1 − ⌊n/2⌋`, the condition (19) is `1 + ⌊n/2⌋ ≤ t` and
`ofReal(n log(32R/d) + log(1/(η²β))) / (2γ_HR) ≤ k` in `ℝ≥0∞`: for `0 < γ_HR < ∞` an integer `k`
is `≥ ⌈x⌉` iff it is `≥ x`; for `γ_HR = 0` the bound is `+∞` (no `t`; the numerator is positive
since `d ≤ R`), and for `γ_HR = ∞` it is `0`. `d` is `Metric.infDist x₀ Kᶜ`; a convex body is a
compact convex set (nonempty interior since `x₀ ∈ interior K`); `log` is natural. `n ≥ 2` is the
standing assumption of App. C.1. The conclusion `IsAlmostLinftyClose η β` adds `D_t ≪ π`, true for
`t ≥ 1` (Lovász–Vempala transition density, cited on p.43). -/
theorem theorem_32 {n : ℕ} (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (R : ℝ)
    (hR : ∃ c, K ⊆ Metric.closedBall c R)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior K)
    (η β : ℝ) (hη : 0 < η) (hη1 : η < 1) (hβ : 0 < β) (hβ1 : β < 1) (t : ℕ)
    (ht : 1 + n / 2 ≤ t)
    (ht' : ENNReal.ofReal ((n : ℝ) * Real.log (32 * R / Metric.infDist x₀ Kᶜ) +
        Real.log (1 / (η ^ 2 * β))) / (2 * HitRunGaps.Spectral.hitRunGap K) ≤
      ((t - (1 + n / 2) : ℕ) : ENNReal)) :
    UnionVolEst.IsAlmostLinftyClose η β (hitRunLaw K x₀ t) (volume[|K]) := by sorry

end UnionVolEst.Supplement

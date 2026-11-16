-- Prove2me | Theorems.Thm_UnionVolEst_Supplement_theorem_21
-- name    : UnionVolEst.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:10:01.905219+00:00
-- url     : https://prove2.me/theorems/15ea2c2b-c8a0-4942-af86-6c18b278a359
-- title:
--   Theorem 21 — Hit-and-Run is $(\varepsilon/32,\varepsilon/(32M))$-almost-$\ell_\infty$-close after $1+\lfloor n/2\rfloor+O(n^2(R/r)^2[n\log(32R/d_0)+\log(32/\varepsilon)+\log M])$ steps
-- statement:
--   This is the walk-length bound for the sampling subroutine of Alpona, also restated as Theorem 31 in Appendix C.
--
--   There is a universal constant $C>0$ with the following property. Let $n\ge1$, and let $K\subseteq\mathbb R^n$ be a convex body that contains a Euclidean ball of radius $r>0$ and is contained in a Euclidean ball of radius $R$. Let $x_0$ be an interior point of $K$ at distance $d_0=\mathrm{dist}(x_0,\partial K)>0$ from the boundary, let $\varepsilon\in(0,1)$ and let $M\ge1$ be an integer. Write $D_t$ for the law of Hit-and-Run started at $x_0$ after $t$ steps, and $\pi$ for the uniform distribution on $K$. Then for every integer
--   $$
--   t\;\ge\;1+\lfloor n/2\rfloor+C\,n^2\Big(\frac Rr\Big)^2\Big[n\log\frac{32R}{d_0}+\log\frac{32}{\varepsilon}+\log M\Big]
--   $$
--   the law $D_t$ is $(\eta,\beta)$-almost-$\ell_\infty$-close to $\pi$ for $\eta=\varepsilon/32$ and $\beta=\varepsilon/(32M)$:
--   $$
--   \pi(\mathrm{Bad}_{t,\eta})\le\beta,\qquad D_t(\mathrm{Bad}_{t,\eta})\le2\beta,
--   $$
--   where $\mathrm{Bad}_{t,\eta}=\{x\in K:|dD_t/d\pi(x)-1|>\eta\}$.
--
--   The theorem bounds the number of Hit-and-Run steps per sample in Alpona's complexity analysis. It improves the $n^3$ dependence of the Lovász–Vempala and Kook–Vempala bounds in the accuracy and stream-length terms to $n^2$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The almost-$\ell_\infty$ closeness used here also asserts $D_t\ll\pi$.
--
--   Differences from the source:
--   - reading: t = 1 + ⌊n/2⌋ + O(n²(R/r)²[n log(32R/d₀) + log(32/ε) + log M]) Hit and Run steps can obtain both bounds → ∃ C > 0, quantified before n, K, r, R, x₀, ε, M, such that every integer t ≥ 1 + ⌊n/2⌋ + C n²(R/r)²[…] gives both bounds; reason: the O(·) hides one universal constant (from Lemma 33's c); every t above the bound works, as the proof through Theorem 32 ('every integer t') gives; the weaker 'some t' reading is not taken
--   - generalization: both bounds in Equation (10), π(Bad_{t,η}) ≤ β and D_t(Bad_{t,η}) ≤ 2β → IsAlmostLinftyClose (ε/32) (ε/(32M)) D_t π, which also asserts D_t ≪ π; reason: the page states that ρ_t = dD_t/dπ exists for t ≥ 1 (p.43); the two bounds are the remaining conjuncts, so the statement specializes to the source
--   - encoding: convex body K ⊂ ℝⁿ with inball radius r and outball radius R, start x₀ with d₀ = dist(x₀, ∂K) > 0 → compact convex K ⊆ EuclideanSpace ℝ (Fin n), 0 < r, ball c r ⊆ K, K ⊆ closedBall c' R, x₀ ∈ interior K, d₀ = Metric.infDist x₀ Kᶜ; reason: same objects; for an interior point the distance to the complement is the distance to the boundary
--   - encoding: ℝⁿ → n ≥ 1; reason: the zero-dimensional space has no unit sphere, so Hit-and-Run is undefined there
--   - encoding: Hit-and-Run (uniform direction on S^{n−1}, uniform point on the chord); log → the published kernel SmithHitAndRun.RandomDir.rdKernel K iterated from δ_{x₀} (hitRunLaw); natural logarithm; reason: same chain
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Theorem 21, §6.2.2, p.30 (PDF p.32), Eq. (14); restated as Theorem 31, App. C, p.43 (PDF p.45), Eq. (18)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_Supplement_hitRunLaw

open MeasureTheory ProbabilityTheory

namespace UnionVolEst.Supplement

/-- Theorem 21 (Bound on the Walk length for the Sampling Subroutine of Alpona)
(Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*,
arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §6.2.2, printed p.30, PDF p.32; restated
as Theorem 31, printed p.43, PDF p.45): there is a universal constant `C > 0` such that for every
convex body `K ⊆ ℝⁿ` containing a ball of radius `r` and contained in a ball of radius `R`, every
start `x₀` in the interior of `K` at distance `d₀ = dist(x₀, ∂K)` from the boundary, every
`ε ∈ (0, 1)` and every `M ≥ 1`, the law `D_t` of Hit-and-Run after `t` steps is
`(ε/32, ε/(32M))`-almost-ℓ∞-close to the uniform distribution on `K` (both bounds of Equation (10))
for every integer
`t ≥ 1 + ⌊n/2⌋ + C n² (R/r)² [n log(32R/d₀) + log(32/ε) + log M]`.

**Formalization Note** The `O(·)` of (14) is one constant `C`, quantified before every other
datum. "Can be obtained in `t` steps" is read as: every `t` at or above the bound works (the
proof goes through Theorem 32, which holds for every such integer). A convex body is a compact
convex set; its interior is nonempty because it contains a ball of radius `r > 0`. `d₀` is
`Metric.infDist x₀ Kᶜ`, the distance from an interior point to the boundary. `log` is the natural
logarithm. `n ≥ 1` excludes the zero-dimensional space, which has no unit sphere. The conclusion
`IsAlmostLinftyClose` also asserts `D_t ≪ π`, which holds for `t ≥ 1` (Lovász–Vempala's
transition density, cited on p.43). -/
theorem theorem_21 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → Convex ℝ K →
        ∀ (r R : ℝ), 0 < r →
          (∃ c, Metric.ball c r ⊆ K) → (∃ c', K ⊆ Metric.closedBall c' R) →
          ∀ (x₀ : EuclideanSpace ℝ (Fin n)), x₀ ∈ interior K →
            ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (M : ℕ), 1 ≤ M →
              ∀ t : ℕ,
                ((1 + n / 2 : ℕ) : ℝ) + C * (n : ℝ) ^ 2 * (R / r) ^ 2 *
                    ((n : ℝ) * Real.log (32 * R / Metric.infDist x₀ Kᶜ) + Real.log (32 / ε) +
                      Real.log M) ≤ (t : ℝ) →
                UnionVolEst.IsAlmostLinftyClose (ε / 32) (ε / (32 * M)) (hitRunLaw K x₀ t)
                  (volume[|K]) := by sorry

end UnionVolEst.Supplement

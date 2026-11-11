-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_theorem_1
-- name    : TightContinualCounting.LowerBounds.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:39.403069+00:00
-- url     : https://prove2.me/theorems/2d07e75a-f789-4edd-b997-71387d4609af
-- title:
--   Theorem 1 — tight lower bounds for all three counting errors
-- statement:
--   Fix the universal constants $c=5/(9\cdot2^{47})$ and $C_0=e^{5500}$. Let $n\ge1$, $0\le\varepsilon\le1$, $0\le\delta\le1/4$, and $\eta=\max\{\varepsilon,\delta\}$. Suppose $n\eta\ge C_0$. Define $L=\log(n\eta)$ and
--
--   $$
--   U=\begin{cases}1+L,&\delta=0,\\1+\min\{L,\log(\eta/\delta)\},&\delta>0.\end{cases}
--   $$
--
--   Every $(\varepsilon,\delta)$-DP binary-prefix mechanism $M$, represented by arbitrary Borel probability laws on $\mathbb R^n$, satisfies all three comparisons
--
--   $$
--   \alpha_\infty(M)\ge c\frac{L^{3/2}\sqrt U}{\eta},\qquad
--   \operatorname{MaxSE}(M)\ge\operatorname{MeanSE}(M)\ge c\frac{L^2U}{\eta^2}.
--   $$
--
--   Here $\alpha_\infty$ is the worst-input expected sup norm, MeanSE the worst-input expected average squared error, and MaxSE the worst-input and coordinate expected squared error. Infinite losses are allowed. The source states universal constants in its asymptotic bound; its own proof on p.15 yields precisely these fixed witnesses. They are independent of every parameter and mechanism.
--
--   This is the full lower bound, with pure DP ($\delta=0$), $\varepsilon=0<\delta$, and all stated endpoints included. It applies also when the mechanism sees the entire stream in advance. The regime $n\eta<C_0$ and achievability are separate appendix results and are outside this theorem.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - encoding: randomized mechanisms and probabilities of measurable events → families of probability measures and event masses in ℝ≥0∞; reason: this is the same model, including arbitrary continuous output laws and infinite loss
--   - encoding: existence of universal c,C₀ in Theorem 1 → the explicit witnesses c=5/(9·2^47), C₀=exp(5500); reason: these are the common constants established by the source proof on p.15, not instance-dependent witnesses
--   - encoding: log(η/0)=+∞ inside min with L → U=1+L at δ=0 and the ordinary logarithm formula otherwise; reason: the branch is exactly the extended-logarithm minimum, so no pure-DP case is lost
--   - encoding: L^(3/2) → L·sqrt(L); reason: the premise implies L≥5500, on which these expressions are equal
--   - encoding: nonnegative expectations and finite maxima defining the three losses → nonnegative extended lower integrals and ENNReal suprema; reason: the same losses are obtained, including infinite expectations, without requiring integrability
--   - encoding: distance at most one in Definition 2 → the published IsDP predicate for distance exactly one; reason: nonnegative ε,δ make the diagonal inequality automatic, without any restriction on mechanisms
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Theorem 1 p.3; proof §§3.3–3.4 pp.10–15, explicit constants p.15

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_TightContinualCounting_LowerBounds_errors
import Definitions.Def_TightContinualCounting_LowerBounds_parameters

open MeasureTheory
open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Full Theorem 1, p.3, with the absolute witnesses established on p.15.
All three metrics and all stated parameter endpoints are included. -/
theorem theorem_1 (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hsize : sizeThreshold ≤ (n : ℝ) * max ε δ)
    (M : (Fin n → Bool) → Measure (Fin n → ℝ)) (hM : ∀ x, IsProbabilityMeasure (M x))
    (hDP : ContinualCounting.IsDP M ε δ) :
    let η := max ε δ
    let L := Real.log ((n : ℝ) * η)
    let U := privacyWindow n ε δ
    ENNReal.ofReal (lowerConstant * (L * Real.sqrt L) * Real.sqrt U / η) ≤
        ContinualCounting.linfError M ∧
      meanSE M ≤ maxSE M ∧
      ENNReal.ofReal (lowerConstant * L ^ 2 * U / η ^ 2) ≤ meanSE M := by sorry

end TightContinualCounting.LowerBounds

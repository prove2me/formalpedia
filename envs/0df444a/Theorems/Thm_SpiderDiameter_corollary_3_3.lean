-- Prove2me | Theorems.Thm_SpiderDiameter_corollary_3_3
-- name    : SpiderDiameter.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:14.821418+00:00
-- url     : https://prove2.me/theorems/ef26c98f-c070-4846-8015-2b5099d72738
-- title:
--   Corollary 3.3, (3.8): value of the two-stage strategy where $y\ge 1/2$, $z\le\varphi(y-1/2)$
-- statement:
--   Let $n\ge3$ and $(x,y,z)\in\mathcal D$ with $y\ge\tfrac12$ and $z\le\varphi(y-\tfrac12)$, and let $\tau^*$ be the two-stage strategy of Step 7. Then $\tau^*<\infty$ almost surely, $G(X_{\tau^*},Y_{\tau^*},Z_{\tau^*})$ is $P_{x,y,z}$-integrable, and
--   $$\mathbb E_{x,y,z}G(X_{\tau^*},Y_{\tau^*},Z_{\tau^*})=\begin{cases} y-z-2(z+\frac12)x+(z+\frac12)^2 & \text{if } x\le f(z)\le0,\\ y-z-\frac{2f(z)}{n-1}x+f(z)^2 & \text{if } x\le0\le f(z),\\ y-z-2f(z)x+f(z)^2 & \text{if } 0\le x\le f(z),\\ y-z-x^2 & \text{if } f(z)\le x\le y-\frac12,\\ y-z-2(y-\frac12)x+(y-\frac12)^2 & \text{if } x\ge y-\frac12,\end{cases}$$
--   where $f=\varphi^{-1}$ is the lower boundary of Steps 5–6.
--
--   This is the first region on which the value of the guessed strategy is computed explicitly; it supplies the boundary values for Corollary 3.5.
--
--   Differences from the source:
--   - encoding: U(x, y, z) = E_{x,y,z} G(X_τ, Y_τ, Z_τ) for the two-stage strategy of Step 7 → the strategy time τ* = inf{t ≥ 0 : f(Z_t) ≤ X_t ≤ Y_t − 1/2} is asserted finite a.s., the gain at τ* integrable, and its Bochner integral equal to the formula; reason: Stage 2's condition implies Stage 1's, so the two stages end at this hitting time; the extra clauses rule out junk values of the integral
--   - reading: φ^{−1} in (3.8) and Corollary 3.5 → the two-branch boundary f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Steps 5–6, p.14; φ is not injective on ℝ, and the paper defines f this way
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - reading: P_{x,y,z}((X_0, Y_0, Z_0) = (x, y, z)) = 1 for every (x, y, z) ∈ D → the start (−y, y, −y), y > 0, is the identified point (y, y, −y) (a ray becomes the longest the moment its rib reaches Y); reason: Remark 3.7: "the points (−y, y, −y) and (y, y, −y) in the state space correspond to the same value of U"; the jump rule of p.11
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Corollary 3.3, eq. (3.8), p.15

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess
import Definitions.Def_SpiderDiameter_ValueFunction

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Corollary 3.3, formula (3.8)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Corollary 3.3,
p.15): "If y ≥ 1/2 and z ≤ φ(y − 1/2), then U(x, y, z) = [the five lines of (3.8)]", where `U` is
the value of the two-stage strategy of Step 7 (p.14).

For every `(x, y, z) ∈ 𝒟` with `y ≥ 1/2` and `z ≤ φ(y − 1/2)`: the strategy time `τ*` is finite
almost surely, the gain `G(X_{τ*}, Y_{τ*}, Z_{τ*})` is integrable under `P_{x,y,z}`, and its
expectation equals (3.8) (`U38`, with `φ⁻¹ = finv n`). -/
theorem corollary_3_3 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (hy : 1 / 2 ≤ y) (hz : z ≤ phi n (y - 1 / 2)) :
    (∀ᵐ ω ∂P, stratTime N x y z ω < ⊤) ∧ Integrable (stratPayoff N x y z) P ∧
      stratValue N x y z = U38 n x y z := by sorry

end SpiderDiameter

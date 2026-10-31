-- Prove2me | Theorems.Thm_SpiderDiameter_corollary_3_6
-- name    : SpiderDiameter.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:52.726501+00:00
-- url     : https://prove2.me/theorems/10cb3f19-d453-46cb-a505-71bb8798d11f
-- title:
--   Corollary 3.6, (3.12)–(3.13) (corrected: $U(1/2,1/2,s)$ from the corrected Corollary 3.5): strategy value where $y<1/2$
-- statement:
--   Let $n\ge3$ and $(x,y,z)\in\mathcal D$ with $y<\tfrac12$, and write $U(\tfrac12,\tfrac12,s)$ for the explicit value on the segment $\{x=y=\tfrac12\}$ given by (3.8) for $s\le-\tfrac12$ and by Corollary 3.5 for $s>-\tfrac12$. Then $\tau^*<\infty$ almost surely, the gain is $P_{x,y,z}$-integrable, and its expectation $U(x,y,z)$ is as follows.
--
--   1. If $x<0$,
--   $$U(x,y,z)=U(\tfrac12,\tfrac12,-y)\,\frac{2((n-1)y-x)}{n-1+2y}+U(\tfrac12,\tfrac12,z)\,\frac{2(x-z)}{n-1-2z}+\int_{-1/2}^{-y}U(\tfrac12,\tfrac12,s)\frac{2n(n-1)}{(n-1-2s)^2}ds+\int_{-y}^{z}U(\tfrac12,\tfrac12,s)\frac{2(n-1-2x)}{(n-1-2s)^2}ds.$$
--   2. If $x\ge0$,
--   $$U(x,y,z)=U(\tfrac12,\tfrac12,-y)\,\frac{2(n-1)(y-x)}{n-1+2y}+U(\tfrac12,\tfrac12,z)\,\frac{2((n-1)x-z)}{n-1-2z}+\int_{-1/2}^{-y}U(\tfrac12,\tfrac12,s)\frac{2n(n-1)}{(n-1-2s)^2}ds+\int_{-y}^{z}U(\tfrac12,\tfrac12,s)\frac{2(n-1)(1-2x)}{(n-1-2s)^2}ds.$$
--
--   At $(x,y,z)=(0,0,0)$, formula (3.13) is the number $U(0,0,0)$ of Theorem 1.1, so this corollary identifies it as the value of the two-stage strategy started at the origin.
--
--   Differences from the source:
--   - reading: U(1/2, 1/2, s) on the right-hand side → the explicit value Uhalf: (3.8) for s ≤ −1/2, Corollary 3.5 for s > −1/2; reason: "The values of U(1/2, 1/2, s) can be extracted from Corollary 3.5" (p.18)
--   - correction: U(1/2, 1/2, s) extracted from the printed Corollary 3.5 → U(1/2, 1/2, s) from Corollary 3.5 with the denominator (n − 1)s − φ(s − 1/2); reason: the printed Corollary 3.5 is false (see Corollary 3.5: continuity across y = 1/2 fails, e.g. 0.94325 vs 0.97892 at n = 3)
--   - encoding: U(x, y, z) = E_{x,y,z} G(X_τ, Y_τ, Z_τ) for the two-stage strategy of Step 7 → the strategy time τ* = inf{t ≥ 0 : f(Z_t) ≤ X_t ≤ Y_t − 1/2} is asserted finite a.s., the gain at τ* integrable, and its Bochner integral equal to the formula; reason: Stage 2's condition implies Stage 1's, so the two stages end at this hitting time; the extra clauses rule out junk values of the integral
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - reading: P_{x,y,z}((X_0, Y_0, Z_0) = (x, y, z)) = 1 for every (x, y, z) ∈ D → the start (−y, y, −y), y > 0, is the identified point (y, y, −y) (a ray becomes the longest the moment its rib reaches Y); reason: Remark 3.7: "the points (−y, y, −y) and (y, y, −y) in the state space correspond to the same value of U"; the jump rule of p.11
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
--   - reading: φ^{−1} in (3.8) and Corollary 3.5 → the two-branch boundary f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Steps 5–6, p.14; φ is not injective on ℝ, and the paper defines f this way
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Corollary 3.6, eq. (3.12), p.17 and eq. (3.13), p.18

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess
import Definitions.Def_SpiderDiameter_ValueFunction

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Corollary 3.6, formulas (3.12) and (3.13)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2,
Corollary 3.6, pp.17–18): "If x < 0 and y < 1/2, then we have (3.12) … For x ≥ 0 and y < 1/2, we
compute that (3.13) …", where `U` on the left is the value of the strategy of Step 7 and
`U(1/2, 1/2, s)` on the right is the value on the segment `{x = y = 1/2}` given by (3.8) and
Corollary 3.5 ("The values of U(1/2, 1/2, s) can be extracted from Corollary 3.5", p.18).

For every `(x, y, z) ∈ 𝒟` with `y < 1/2`: `τ* < ∞` almost surely, the gain is integrable, and
1. if `x < 0`, the strategy value is
   `U(1/2,1/2,−y)·2((n−1)y − x)/(n−1+2y) + U(1/2,1/2,z)·2(x − z)/(n−1−2z)
    + ∫_{−1/2}^{−y} U(1/2,1/2,s)·2n(n−1)/(n−1−2s)² ds + ∫_{−y}^{z} U(1/2,1/2,s)·2(n−1−2x)/(n−1−2s)² ds`;
2. if `x ≥ 0`, it is
   `U(1/2,1/2,−y)·2(n−1)(y − x)/(n−1+2y) + U(1/2,1/2,z)·2((n−1)x − z)/(n−1−2z)
    + ∫_{−1/2}^{−y} U(1/2,1/2,s)·2n(n−1)/(n−1−2s)² ds + ∫_{−y}^{z} U(1/2,1/2,s)·2(n−1)(1−2x)/(n−1−2s)² ds`.

**Formalization Note (reading).** `U(1/2, 1/2, s)` is the explicit value `Uhalf n s`: (3.8) for
`s ≤ −1/2` and Corollary 3.5 (with the corrected integrand) for `s > −1/2`. -/
theorem corollary_3_6 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (hy : y < 1 / 2) :
    (∀ᵐ ω ∂P, stratTime N x y z ω < ⊤) ∧ Integrable (stratPayoff N x y z) P ∧
    (x < 0 → stratValue N x y z =
      Uhalf n (-y) * (2 * (((n : ℝ) - 1) * y - x) / ((n : ℝ) - 1 + 2 * y))
        + Uhalf n z * (2 * (x - z) / ((n : ℝ) - 1 - 2 * z))
        + (∫ s in (-1 / 2 : ℝ)..(-y),
            Uhalf n s * (2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 1 - 2 * s) ^ 2))
        + ∫ s in (-y)..z, Uhalf n s * (2 * ((n : ℝ) - 1 - 2 * x) / ((n : ℝ) - 1 - 2 * s) ^ 2)) ∧
    (0 ≤ x → stratValue N x y z =
      Uhalf n (-y) * (2 * ((n : ℝ) - 1) * (y - x) / ((n : ℝ) - 1 + 2 * y))
        + Uhalf n z * (2 * (((n : ℝ) - 1) * x - z) / ((n : ℝ) - 1 - 2 * z))
        + (∫ s in (-1 / 2 : ℝ)..(-y),
            Uhalf n s * (2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 1 - 2 * s) ^ 2))
        + ∫ s in (-y)..z,
            Uhalf n s * (2 * ((n : ℝ) - 1) * (1 - 2 * x) / ((n : ℝ) - 1 - 2 * s) ^ 2)) := by sorry

end SpiderDiameter

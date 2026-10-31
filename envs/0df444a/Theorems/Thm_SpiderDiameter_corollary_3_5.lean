-- Prove2me | Theorems.Thm_SpiderDiameter_corollary_3_5
-- name    : SpiderDiameter.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:40.242553+00:00
-- url     : https://prove2.me/theorems/1eddb305-ad87-4e6c-b315-452bfed93092
-- title:
--   Corollary 3.5 (corrected: integrand $\varphi(s-1/2)$): strategy value where $y\ge1/2$, $z>\varphi(y-1/2)$
-- statement:
--   Let $n\ge3$ and $(x,y,z)\in\mathcal D$ with $y\ge\tfrac12$ and $z>\varphi(y-\tfrac12)$. Then $\tau^*<\infty$ almost surely, the gain $G(X_{\tau^*},Y_{\tau^*},Z_{\tau^*})$ is $P_{x,y,z}$-integrable, and its expectation $U(x,y,z)$ equals
--   $$U\big(x,f(z)+\tfrac12,z\big)-\int_y^{f(z)+1/2}\frac{(n-1)(s-x)}{(n-1)s-\varphi(s-\frac12)}\,ds \quad\text{if } x\ge0,$$
--   $$U\big(x,f(z)+\tfrac12,z\big)-\int_y^{f(z)+1/2}\frac{(n-1)s-x}{(n-1)s-\varphi(s-\frac12)}\,ds \quad\text{if } x<0,$$
--   where $U(x,f(z)+\tfrac12,z)$ is the explicit value (3.8) at the point $(x,f(z)+\tfrac12,z)$, which lies in the region of Corollary 3.3 because $z=\varphi(f(z))$.
--
--   Together with Corollary 3.3 this gives the strategy value on $\{y\ge\tfrac12\}$, in particular on the segment $\{x=y=\tfrac12\}$ used in Corollary 3.6.
--
--   Differences from the source:
--   - correction: Corollary 3.5 integrand (n − 1)(s − x)/((n − 1)s − φ(y − 1/2)) (and ((n − 1)s − x)/(…) for x ≤ 0) → denominator (n − 1)s − φ(s − 1/2); reason: the printed version contradicts (3.9) of Lemma 3.4, which it integrates, and continuity of U across y = 1/2: at n = 3, (x, z) = (−0.05, −0.1), (3.12) tends to 0.94325 as y ↑ 1/2 while the printed formula gives 0.97892 at y = 1/2 (corrected: 0.94325); at n = 2 the printed chain gives U(0,0,0) = 0.7616 instead of the known 3/4
--   - reading: U(x, f(z) + 1/2, z) on the right-hand side → the explicit (3.8) value at (x, f(z) + 1/2, z); reason: that point lies in the region of Corollary 3.3, whose value the corollary extends ("Lemma 3.4 allows us to extend the formula for U", p.17)
--   - encoding: cases x ≥ 0 and x ≤ 0 → cases x ≥ 0 and x < 0; reason: the two printed formulas agree at x = 0
--   - reading: φ^{−1} in (3.8) and Corollary 3.5 → the two-branch boundary f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Steps 5–6, p.14; φ is not injective on ℝ, and the paper defines f this way
--   - encoding: U(x, y, z) = E_{x,y,z} G(X_τ, Y_τ, Z_τ) for the two-stage strategy of Step 7 → the strategy time τ* = inf{t ≥ 0 : f(Z_t) ≤ X_t ≤ Y_t − 1/2} is asserted finite a.s., the gain at τ* integrable, and its Bochner integral equal to the formula; reason: Stage 2's condition implies Stage 1's, so the two stages end at this hitting time; the extra clauses rule out junk values of the integral
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Corollary 3.5, p.17 (corrected integrand; (3.9) of Lemma 3.4, p.15)

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess
import Definitions.Def_SpiderDiameter_ValueFunction

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Corollary 3.5, corrected** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Corollary 3.5,
p.17): "If y ≥ 1/2 and z > φ(y − 1/2), then U(x, y, z) = U(x, f(z) + 1/2, z) −
∫_y^{f(z)+1/2} (n − 1)(s − x)ds/((n − 1)s − φ(y − 1/2)) if x ≥ 0, and U(x, f(z) + 1/2, z) −
∫_y^{f(z)+1/2} ((n − 1)s − x)ds/((n − 1)s − φ(y − 1/2)) if x ≤ 0", where `U` is the value of the
strategy of Step 7.

Corrected statement: for every `(x, y, z) ∈ 𝒟` with `y ≥ 1/2` and `z > φ(y − 1/2)`: `τ* < ∞`
almost surely, the gain is integrable, and the strategy value equals (3.8) at the point
`(x, f(z) + 1/2, z)` minus `∫_y^{f(z)+1/2} (n − 1)(s − x)/((n − 1)s − φ(s − 1/2)) ds` (for `x ≥ 0`),
respectively `∫_y^{f(z)+1/2} ((n − 1)s − x)/((n − 1)s − φ(s − 1/2)) ds` (for `x < 0`).

**Formalization Note (correction).** The printed denominator `(n − 1)s − φ(y − 1/2)` is corrected
to `(n − 1)s − φ(s − 1/2)`: the corollary integrates (3.9) of Lemma 3.4 in `y`, and the printed
version contradicts both (3.9) and continuity of the strategy value across `y = 1/2` (at `n = 3`,
`(x, z) = (−0.05, −0.1)`: (3.12) tends to `0.94325` as `y ↑ 1/2`, the printed formula gives
`0.97892` at `y = 1/2`, the corrected one `0.94325`).
**Formalization Note (reading).** `U(x, f(z) + 1/2, z)` on the right is the value already computed
in Corollary 3.3 at that point, i.e. (3.8) (`U38`), since `z = φ(f(z))` puts the point in the
region of (3.8). -/
theorem corollary_3_5 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (hy : 1 / 2 ≤ y) (hz : phi n (y - 1 / 2) < z) :
    (∀ᵐ ω ∂P, stratTime N x y z ω < ⊤) ∧ Integrable (stratPayoff N x y z) P ∧
      stratValue N x y z =
        if 0 ≤ x then
          U38 n x (finv n z + 1 / 2) z - ∫ s in y..(finv n z + 1 / 2),
            ((n : ℝ) - 1) * (s - x) / (((n : ℝ) - 1) * s - phi n (s - 1 / 2))
        else
          U38 n x (finv n z + 1 / 2) z - ∫ s in y..(finv n z + 1 / 2),
            (((n : ℝ) - 1) * s - x) / (((n : ℝ) - 1) * s - phi n (s - 1 / 2)) := by sorry

end SpiderDiameter

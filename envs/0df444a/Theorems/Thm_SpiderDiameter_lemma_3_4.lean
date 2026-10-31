-- Prove2me | Theorems.Thm_SpiderDiameter_lemma_3_4
-- name    : SpiderDiameter.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:08.225798+00:00
-- url     : https://prove2.me/theorems/acabe5a1-9707-4da0-9d0b-bf85448a3c38
-- title:
--   Lemma 3.4, (3.9): the $y$-derivative of the strategy value where $y\ge1/2$, $z>\varphi(y-1/2)$
-- statement:
--   Let $n\ge3$ and $(x,y,z)\in\mathcal D$ with $y\ge\tfrac12$ and $z>\varphi(y-\tfrac12)$, and let $U(x,w,z)=\mathbb E_{x,w,z}G(X_{\tau^*},Y_{\tau^*},Z_{\tau^*})$ be the value of the two-stage strategy. Then the gain of the strategy is integrable from every $(x,w,z)\in\mathcal D$, and
--   $$U_y(x,y,z)=\begin{cases}\dfrac{(n-1)(y-x)}{(n-1)y-\varphi(y-\frac12)} & \text{if } x\ge0,\\[8pt] \dfrac{(n-1)y-x}{(n-1)y-\varphi(y-\frac12)} & \text{if } x\le0,\end{cases}$$
--   the derivative in $w$ at $w=y$ being taken within $\{w: (x,w,z)\in\mathcal D\}$.
--
--   Integrating this derivative in $y$ gives Corollary 3.5.
--
--   **Formalization Note** $U$ lives on $\mathcal D$, so the derivative is taken within $\mathcal D$. Under the hypotheses $-z<\tfrac12\le y$, so this is the ordinary two-sided derivative at every $y>x$, including $y=\tfrac12$, where the region of (3.12)–(3.13) begins on the left; it is one-sided only at $y=x$, the boundary of $\mathcal D$.
--
--   Differences from the source:
--   - encoding: U_y(x, y, z) → HasDerivWithinAt in w at y within {w : (x, w, z) ∈ D}; reason: the domain of U is D; this is the two-sided derivative at every y > x, including y = 1/2, and one-sided only at y = x, the boundary of D
--   - encoding: U = E G(X_τ, Y_τ, Z_τ) for the strategy of Step 7 → the gain is asserted integrable from every (x, w, z) ∈ D; the strategy value is a Bochner integral; reason: excludes junk values of the integral near y
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
--   - encoding: cases x ≥ 0 and x ≤ 0 → cases x ≥ 0 and x < 0; reason: the two printed formulas agree at x = 0
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Lemma 3.4, eq. (3.9), p.15

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess
import Definitions.Def_SpiderDiameter_ValueFunction

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Lemma 3.4, formula (3.9)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Lemma 3.4, p.15):
"Let y ≥ 1/2 and z > φ(y − 1/2). The function U satisfies
U_y(x, y, z) = (n − 1)(y − x)/((n − 1)y − φ(y − 1/2)) if x ≥ 0, ((n − 1)y − x)/((n − 1)y − φ(y − 1/2))
if x ≤ 0", where `U` is the value of the strategy of Step 7.

For every `(x, y, z) ∈ 𝒟` with `y ≥ 1/2` and `z > φ(y − 1/2)`: the strategy's gain is integrable
from every point `(x, w, z) ∈ 𝒟`, and `w ↦ U(x, w, z)` has derivative (3.9) at `w = y` within
`{w : (x, w, z) ∈ 𝒟}`.

**Formalization Note.** `U` lives on `𝒟`, so the derivative is taken within `𝒟`. Under the
hypotheses `−z < 1/2 ≤ y`, hence this is the ordinary two-sided derivative `U_y` at every `y > x`,
including `y = 1/2`, where the region of (3.12)–(3.13) begins on the left; it is one-sided only at
`y = x`, the boundary of `𝒟`. The two formulas agree at `x = 0`; the first is used for `x ≥ 0`. -/
theorem lemma_3_4 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (hy : 1 / 2 ≤ y) (hz : phi n (y - 1 / 2) < z) :
    (∀ w : ℝ, (x, w, z) ∈ stateSpace → Integrable (stratPayoff N x w z) P) ∧
    HasDerivWithinAt (fun w => stratValue N x w z)
      (if 0 ≤ x then ((n : ℝ) - 1) * (y - x) / (((n : ℝ) - 1) * y - phi n (y - 1 / 2))
       else (((n : ℝ) - 1) * y - x) / (((n : ℝ) - 1) * y - phi n (y - 1 / 2)))
      {w : ℝ | (x, w, z) ∈ stateSpace} y := by sorry

end SpiderDiameter

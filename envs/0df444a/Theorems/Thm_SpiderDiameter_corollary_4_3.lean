-- Prove2me | Theorems.Thm_SpiderDiameter_corollary_4_3
-- name    : SpiderDiameter.corollary_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:46.944538+00:00
-- url     : https://prove2.me/theorems/49214657-8b7e-4ad5-b124-5b28a276043b
-- title:
--   Corollary 4.3 (corrected $U$: Corollary 3.5 integrand $\varphi(s-1/2)$): the value function (3.3) equals the candidate on $\mathcal D$
-- statement:
--   Let $n\ge3$. For every $(x,y,z)\in\mathcal D$, the set of expected gains $\mathbb E_{x,y,z}G(X_\tau,Y_\tau,Z_\tau)$ over integrable stopping times $\tau$ of $X$ is bounded above, and its supremum, the value function $\mathbb U(x,y,z)$ of (3.3), equals the explicit candidate:
--   $$\mathbb U(x,y,z)=U(x,y,z).$$
--
--   This identifies the solution of the optimal stopping problem, and at the origin gives the constant of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: 𝕌 = sup E G(X_τ, Y_τ, Z_τ) over integrable stopping times of X → sSup in ℝ of the expectations over integrable stopping times of X with integrable gain; boundedness above asserted; reason: the positive part of the gain is integrable for integrable τ, so excluded times have expectation −∞ and do not change the supremum; boundedness rules out the junk sSup
--   - correction: U built with the printed Corollary 3.5 (integrand denominator (n − 1)s − φ(y − 1/2)) → the candidate U uses the corrected denominator (n − 1)s − φ(s − 1/2) on {y ≥ 1/2, z > φ(y − 1/2)} and in U(1/2, 1/2, s); reason: the printed Corollary 3.5 contradicts Lemma 3.4 and continuity of U across y = 1/2 (n = 3, (x, z) = (−0.05, −0.1): 0.94325 from (3.12) vs 0.97892 printed); see Corollary 3.5
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - reading: P_{x,y,z}((X_0, Y_0, Z_0) = (x, y, z)) = 1 for every (x, y, z) ∈ D → the start (−y, y, −y), y > 0, is the identified point (y, y, −y) (a ray becomes the longest the moment its rib reaches Y); reason: Remark 3.7: "the points (−y, y, −y) and (y, y, −y) in the state space correspond to the same value of U"; the jump rule of p.11
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
--   - reading: U of Section 3 (from Step 7 on, the strategy value) → the explicit function glued from (3.8), Corollary 3.5 and (3.12)–(3.13), with φ^{−1} the two-branch f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Section 4 treats "the function U constructed in the previous section" and Remark 3.7 compares lines of (3.8); Corollaries 3.3, 3.5 and 3.6 identify that function with the strategy value
--   - encoding: integrable stopping time τ of X → τ : Ω → [0, ∞] with {τ ≤ t} ∈ σ(X_s : s ≤ t) for every t and ∫⁻ τ dP < ∞; the processes take their time-0 values on the null set {τ = ∞}; reason: the class of (3.3), with Mathlib's {τ ≤ t} convention
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Corollary 4.3, p.20; value function (3.3), p.13

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess
import Definitions.Def_SpiderDiameter_ValueFunction

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Corollary 4.3** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Corollary 4.3, p.20): "We
have 𝕌 = U on D", where `𝕌` is the value function (3.3) and `U` the explicit candidate of §3.

For every `(x, y, z) ∈ 𝒟`, the set of expected gains `E_{x,y,z} G(X_τ, Y_τ, Z_τ)` over integrable
stopping times `τ` of `X` is bounded above, and its supremum `𝕌(x, y, z)` equals the candidate
`U(x, y, z)`. -/
theorem corollary_4_3 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace) :
    BddAbove (valueSet P N x y z) ∧ valueFn P N x y z = candidate n x y z := by sorry

end SpiderDiameter

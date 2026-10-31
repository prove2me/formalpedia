-- Prove2me | Theorems.Thm_SpiderDiameter_lemma_3_1
-- name    : SpiderDiameter.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:39.77002+00:00
-- url     : https://prove2.me/theorems/360c80f0-d023-44b8-a753-c11871193e2e
-- title:
--   Lemma 3.1 (corrected: time scale $t/\lambda^2$): Brownian scaling of $(X,Y,Z)$
-- statement:
--   Let $n\ge3$, $(x,y,z)\in\mathcal D$ and $\lambda>0$. Then the process
--   $$t\mapsto\big(\lambda X_{t/\lambda^2},\ \lambda Y_{t/\lambda^2},\ \lambda Z_{t/\lambda^2}\big)$$
--   under $P_{x,y,z}$ has the same law, as a random element of the path space $(\mathbb R^3)^{[0,\infty)}$ with its product $\sigma$-algebra, as $(X,Y,Z)$ under $P_{\lambda x,\lambda y,\lambda z}$. Both path processes are almost everywhere measurable.
--
--   This is the scaling used in the proof of Theorem 1.1 to pass from the additive inequality $\mathbb E D_\tau-\mathbb E\tau\le U(0,0,0)$ to the multiplicative one.
--
--   **Formalization Note** The law equality is an equality of push-forward measures, with almost-everywhere measurability of both maps stated so that neither side can be the zero measure.
--
--   Differences from the source:
--   - correction: time change t ↦ tλ^{−1/2} → time change t ↦ t/λ²; reason: the printed statement is false: at (x,y,z) = (0,0,0), λ = 4, t = 1, E(4X_{1/2})² = 16·(1/2) = 8 while E X_1² = 1 under P_{0,0,0} (|X| is reflecting Brownian motion); t/λ² is Brownian scaling, used by the paper on p.20
--   - encoding: "has the same law" → equality of the push-forward measures on ℝ≥0 → ℝ × ℝ × ℝ (product σ-algebra), with AEMeasurable of both path maps; reason: law of a process = law of its path; the measurability clauses exclude the junk zero measure
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - reading: P_{x,y,z}((X_0, Y_0, Z_0) = (x, y, z)) = 1 for every (x, y, z) ∈ D → the start (−y, y, −y), y > 0, is the identified point (y, y, −y) (a ray becomes the longest the moment its rib reaches Y); reason: Remark 3.7: "the points (−y, y, −y) and (y, y, −y) in the state space correspond to the same value of U"; the jump rule of p.11
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Lemma 3.1, p.11 (corrected time scale; cf. the scaling (λX_{t/λ²}) on p.20)

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_GeneralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Lemma 3.1 (Brownian scaling), corrected** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2,
Lemma 3.1, p.11): "For any λ > 0, the process t ↦ (λX_{tλ^{−1/2}}, λY_{tλ^{−1/2}}, λZ_{tλ^{−1/2}})
has the same law under P_{x,y,z} as does (X, Y, Z) under P_{λx,λy,λz}."

Corrected statement: for every `(x, y, z) ∈ 𝒟` and `λ > 0`, the path process
`t ↦ (λX_{t/λ²}, λY_{t/λ²}, λZ_{t/λ²})` started from `(x, y, z)` and the path process
`t ↦ (X_t, Y_t, Z_t)` started from `(λx, λy, λz)` are a.e.-measurable random elements of
`ℝ≥0 → ℝ × ℝ × ℝ` (product σ-algebra) with the same law.

**Formalization Note (correction).** The printed time change `tλ^{−1/2}` is false: at
`(x,y,z) = (0,0,0)`, `λ = 4`, `t = 1`, `E(4X_{1/2})² = 8` while `E X_1² = 1`. The time change
`t/λ²` is the Brownian one, used by the paper itself on p.20. -/
theorem lemma_3_1 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (lam : ℝ≥0) (hlam : 0 < lam) :
    AEMeasurable (fun ω (t : ℝ≥0) => ((lam : ℝ) * Xg N x y z (t / lam ^ 2) ω,
        (lam : ℝ) * Yg N x y z (t / lam ^ 2) ω, (lam : ℝ) * Zg N x y z (t / lam ^ 2) ω)) P ∧
    AEMeasurable (fun ω (t : ℝ≥0) => (Xg N (lam * x) (lam * y) (lam * z) t ω,
        Yg N (lam * x) (lam * y) (lam * z) t ω, Zg N (lam * x) (lam * y) (lam * z) t ω)) P ∧
    P.map (fun ω (t : ℝ≥0) => ((lam : ℝ) * Xg N x y z (t / lam ^ 2) ω,
        (lam : ℝ) * Yg N x y z (t / lam ^ 2) ω, (lam : ℝ) * Zg N x y z (t / lam ^ 2) ω)) =
      P.map (fun ω (t : ℝ≥0) => (Xg N (lam * x) (lam * y) (lam * z) t ω,
        Yg N (lam * x) (lam * y) (lam * z) t ω, Zg N (lam * x) (lam * y) (lam * z) t ω)) := by sorry

end SpiderDiameter

-- Prove2me | Theorems.Thm_RandAssort_theorem_1
-- name    : RandAssort.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:07.638005+00:00
-- url     : https://prove2.me/theorems/dbe7c04d-167a-4cfe-9d77-b22959baf51b
-- title:
--   Theorem 1: randomization-proof iff some $\mathbb Q\in\mathcal P(\mathcal U)$ has $\mathbb E_{\mathbb Q}[R(S,\tilde u)]\le R^\star_{\mathrm{det}}$ for all $S$ (corrected: lsc added for "only if")
-- statement:
--   Fix a robust assortment optimization instance $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$ satisfying the standing assumptions of §3: $\mathcal S$ and $\mathcal U$ are nonempty, $\mathcal U$ is a compact subset of a finite-dimensional real normed space, prices are positive, and $\mathfrak C(\cdot\mid S,u)$ is a probability distribution on $\mathcal N_0$ that vanishes on products outside $S$. If for every $S\in\mathcal S$ the expected revenue $u\mapsto R(S,u)$ is lower semicontinuous on $\mathcal U$, then the instance is randomization-proof, i.e. $R^\star_{\mathrm{rand}}(\mathcal U)\le R^\star_{\mathrm{det}}(\mathcal U)$, if and only if there is $\mathbb Q\in\mathcal P(\mathcal U)$ such that
--   $$
--   \mathbb E_{\mathbb Q}[R(S,\tilde u)]\le R^\star_{\mathrm{det}}(\mathcal U)\qquad\text{for all } S\in\mathcal S,
--   $$
--   where $\mathcal P(\mathcal U)$ denotes the set of all probability distributions supported on $\mathcal U$. The "if" half holds for every instance, without the semicontinuity hypothesis: if such a $\mathbb Q$ exists, the instance is randomization-proof.
--
--   The distribution $\mathbb Q$ is a certificate that randomizing over assortments cannot raise the worst-case expected revenue above the deterministic robust value. Sections 4–6 of the paper apply this criterion to the MNL, Markov chain and preference-ranking models. In all three, $u\mapsto\mathfrak C(i\mid S,u)$ is continuous, which implies the lower semicontinuity hypothesis.
--
--   **Formalization Note** $\mathcal P(\mathcal U)$ is the set of Borel probability measures on $\mathcal U$, viewed as a subspace. The expectation is the Bochner integral over $\mathcal U$, and the condition also requires $u\mapsto R(S,u)$ to be $\mathbb Q$-integrable, so that the expectation is defined. Under the semicontinuity hypothesis this function is bounded and Borel, so it is always integrable. $R^\star_{\mathrm{det}}$ and $R^\star_{\mathrm{rand}}$ are the paper's max–min values, written as real suprema and infima.
--
--   Differences from the source:
--   - correction: no continuity of ℭ or of u ↦ R(S,u) (only 𝒰 compact) → for the 'only if' half (and the iff stated under it), for every S ∈ 𝒮, u ↦ R(S,u) lower semicontinuous on 𝒰; the 'if' half is stated separately without it; reason: the printed 'only if' half is false: n = 2, 𝒮 = {{1},{2}}, r = (2,2), 𝒰 = [0,1], ℭ(1|{1},s) = (1+s²)/2, ℭ(2|{2},s) = (1−s)/2 for s ∈ (0,1] and ℭ(1|{1},0) = 1/2, ℭ(2|{2},0) = 1 (no-purchase takes the rest) satisfy every assumption and give (R({1},s), R({2},s)) = (1+s², 1−s) for s > 0 and (1,2) at s = 0; the instance is randomization-proof (R⋆_rand = R⋆_det = 1, all minima attained), but E_ℚ[R({1},ũ)] ≤ 1 forces ℚ({0}) = 1 and then E_ℚ[R({2},ũ)] = 2 > 1, so no ℚ exists
--   - reading: 𝒫(𝒰), 'all probability distributions supported on 𝒰' → Borel probability measures on the subspace 𝒰; reason: the standard meaning; it is the larger of the candidate classes, so the 'only if' half asks for no more than the source and the 'if' half assumes no more
--   - reading: E_ℚ[R(S,ũ)] → u ↦ R(S,u) ℚ-integrable and its Bochner integral; reason: the expectation must exist for the condition to make sense; R(S,·) is bounded, so integrability only asks that it be ℚ-measurable, and under the lsc hypothesis (the 'only if' half) it is Borel and integrable for every ℚ, so there the clause excludes nothing
--   - encoding: products {1,…,n}, alternatives 𝒩₀ = 𝒩 ∪ {0} with r₀ = 0, a compact subset of a finite-dimensional space → Fin n, Option (Fin n) with none the no-purchase option, revenue summed over offered products, 𝒰 a subset of a finite-dimensional real normed space with its Borel σ-algebra; reason: Lean convention; same instances
--   - encoding: max over 𝒮 and Δ(𝒮), min over 𝒰; 𝒮, 𝒰 implicitly nonempty → real ⨆ and ⨅; 𝒮, 𝒰 nonempty in the validity predicate; reason: the extrema are undefined over empty sets; under the hypotheses they are attained and equal the suprema and infima
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, Theorem 1, p.9; instance and standing assumptions §3, pp.7–8; Definition 1, p.8

import Mathlib
import Definitions.Def_RandAssort_Model

open MeasureTheory

namespace RandAssort

/-- **Theorem 1**, p.9 of Z. Wang, H. Peura, W. Wiesemann, *Randomized Assortment Optimization*,
Operations Research (2024), doi:10.1287/opre.2022.0129 (corrected: lower semicontinuity of
`u ↦ R(S, u)` added for the "only if" half).

Fix a robust assortment optimization instance `(𝒩, 𝒮, ℭ, 𝒰, r)` satisfying the assumptions of
§3 (`Instance.IsValid`) in a finite-dimensional real normed space.

1. If for every `S ∈ 𝒮` the expected revenue `u ↦ R(S, u)` is lower semicontinuous on `𝒰`, then
   the instance is randomization-proof if and only if there is `ℚ ∈ 𝒫(𝒰)` such that
   `E_ℚ[R(S, ũ)] ≤ R⋆_det(𝒰)` for all `S ∈ 𝒮`, where `𝒫(𝒰)` denotes the set of all probability
   distributions supported on `𝒰`.
2. The "if" half holds for every instance, with no semicontinuity: if some `ℚ ∈ 𝒫(𝒰)` has
   `E_ℚ[R(S, ũ)] ≤ R⋆_det(𝒰)` for all `S ∈ 𝒮`, the instance is randomization-proof.

**Formalization Note**
* `𝒫(𝒰)` is `MeasureTheory.ProbabilityMeasure 𝒰`, the Borel probability measures on `𝒰` as a
  subspace of `E`; `E_ℚ[R(S, ũ)]` is the Bochner integral of `u ↦ R(S, u)` over `𝒰`, required to
  be `ℚ`-integrable, so that the expectation is defined (under the lower semicontinuity
  hypothesis it always is: the function is bounded and lower semicontinuous, hence Borel).
* `R⋆_det(𝒰)` and `R⋆_rand(𝒰)` are the max–min values of §3 (`Instance.Rdet`,
  `Instance.Rrand`), written as real suprema and infima; randomization-proof is Definition 1,
  `¬ (R⋆_rand(𝒰) > R⋆_det(𝒰))`.
* The lower semicontinuity hypothesis is not in the paper, which assumes only that `𝒰` is
  compact. It is required only for the "only if" half (clause 2 states the "if" half without it).
  Without it the "only if" half fails: `n = 2`, `𝒮 = {{1},{2}}`, `r = (2,2)`,
  `𝒰 = [0,1]`, with `(R({1},s), R({2},s)) = (1 + s², 1 − s)` for `s > 0` and `(1, 2)` at `s = 0`,
  is randomization-proof (`R⋆_rand = R⋆_det = 1`, all minima attained), but no `ℚ` exists. -/
theorem theorem_1 {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (I : Instance n E) (hI : I.IsValid) :
    ((∀ S ∈ I.S, LowerSemicontinuousOn (fun u => I.R S u) I.U) →
      (I.RandomizationProof ↔
        ∃ Q : ProbabilityMeasure I.U, ∀ S ∈ I.S,
          Integrable (fun u : I.U => I.R S u) (Q : Measure I.U) ∧
          ∫ u, I.R S u ∂(Q : Measure I.U) ≤ I.Rdet)) ∧
    ((∃ Q : ProbabilityMeasure I.U, ∀ S ∈ I.S,
        Integrable (fun u : I.U => I.R S u) (Q : Measure I.U) ∧
        ∫ u, I.R S u ∂(Q : Measure I.U) ≤ I.Rdet) →
      I.RandomizationProof) := by sorry

end RandAssort

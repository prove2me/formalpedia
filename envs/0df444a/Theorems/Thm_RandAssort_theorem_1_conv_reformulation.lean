-- Prove2me | Theorems.Thm_RandAssort_theorem_1_conv_reformulation
-- name    : RandAssort.theorem_1_conv_reformulation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:32:00.817172+00:00
-- url     : https://prove2.me/theorems/3bed379e-9c93-4825-9c4f-6418061b8e80
-- title:
--   Proof of Theorem 1: some $\mathbb Q\in\mathcal P(\mathcal U)$ has $\mathbb E_{\mathbb Q}[R(S,\tilde u)]\le c$ for all $S$ iff some $R'\in\operatorname{conv}\mathcal R$ has $R'\le c\cdot\mathbf e$
-- statement:
--   Let $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$ be a robust assortment instance satisfying the standing assumptions of §3, with $\mathcal U$ a compact subset of a finite-dimensional real normed space. Let $\mathcal R$ be its set of expected revenue vectors, $\mathbf e$ the all-ones vector, and $c$ a real number. The following are equivalent:
--
--   1. there is a probability distribution $\mathbb Q\in\mathcal P(\mathcal U)$ such that, for every $S\in\mathcal S$, the expectation $\mathbb E_{\mathbb Q}[R(S,\tilde u)]$ exists and
--   $$
--   \mathbb E_{\mathbb Q}[R(S,\tilde u)]\le c;
--   $$
--   2. there is $R'\in\operatorname{conv}\mathcal R$ with $R'\le c\cdot\mathbf e$ componentwise.
--
--   With $c=R^\star_{\mathrm{det}}(\mathcal U)$ this restates the condition of Theorem 1 in terms of the convex hull of the revenue vectors. The rest of the proof works with that form.
--
--   **Formalization Note** $\mathcal P(\mathcal U)$ is the set of Borel probability measures on $\mathcal U$, viewed as a subspace. The expectation is the Bochner integral over $\mathcal U$, and "exists" means that $u\mapsto R(S,u)$ is $\mathbb Q$-integrable. No continuity of $u\mapsto R(S,u)$ is assumed.
--
--   Differences from the source:
--   - generalization: threshold R⋆_det(𝒰) → an arbitrary real c; reason: the statement at c = R⋆_det(𝒰) is the source's
--   - reading: 𝒫(𝒰), 'all probability distributions supported on 𝒰', and E_ℚ[R(S,ũ)] → Borel probability measures on the subspace 𝒰, with u ↦ R(S,u) required to be ℚ-integrable and E_ℚ its Bochner integral; reason: the expectation of the bounded function R(S,·) is meaningful exactly when it is ℚ-integrable
--   - encoding: products {1,…,n}, alternatives 𝒩₀ = 𝒩 ∪ {0} with r₀ = 0, a compact subset of a finite-dimensional space; 𝒮, 𝒰 implicitly nonempty → Fin n, Option (Fin n) with none the no-purchase option, revenue summed over offered products, 𝒰 a subset of a finite-dimensional real normed space; 𝒮, 𝒰 nonempty in the validity predicate; reason: Lean convention; same instances
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, proof of Theorem 1, e-companion p.ec8 (and p.ec9, "As discussed before, this is equivalent to …")

import Mathlib
import Definitions.Def_RandAssort_Model
import Definitions.Def_RandAssort_RevenueVectors

open MeasureTheory

namespace RandAssort

/-- **Proof of Theorem 1**, e-companion pp.ec8–ec9 of Z. Wang, H. Peura, W. Wiesemann,
*Randomized Assortment Optimization*, Operations Research (2024), doi:10.1287/opre.2022.0129:
the condition of Theorem 1 in convex-hull form.

For a valid instance and every real threshold `c`: there is a probability distribution `ℚ` on `𝒰`
with `E_ℚ[R(S, ũ)] ≤ c` for all `S ∈ 𝒮` if and only if there is `R′ ∈ conv ℛ` with `R′ ≤ c · e`
(componentwise). The paper uses `c = R⋆_det(𝒰)`.

**Formalization Note** `𝒫(𝒰)` is the set of Borel probability measures on `𝒰` (as a subspace of
`E`), `MeasureTheory.ProbabilityMeasure 𝒰`, and `E_ℚ[R(S, ũ)]` is the Bochner integral of
`u ↦ R(S, u)` over `𝒰`. The condition requires this function to be `ℚ`-integrable, so that the
expectation is meaningful (the Bochner integral of a non-integrable function would be `0`).
No continuity of `u ↦ R(S, u)` is assumed. -/
theorem theorem_1_conv_reformulation {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (I : Instance n E) (hI : I.IsValid) (c : ℝ) :
    (∃ Q : ProbabilityMeasure I.U, ∀ S ∈ I.S,
        Integrable (fun u : I.U => I.R S u) (Q : Measure I.U) ∧
        ∫ u, I.R S u ∂(Q : Measure I.U) ≤ c) ↔
      ∃ R' ∈ convexHull ℝ I.revSet, ∀ S : I.S, R' S ≤ c := by sorry

end RandAssort

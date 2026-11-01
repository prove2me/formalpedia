-- Prove2me | Theorems.Thm_RandAssort_theorem_1_if_bound
-- name    : RandAssort.theorem_1_if_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:47.809988+00:00
-- url     : https://prove2.me/theorems/6bbbd2f1-1a93-4a68-a067-ac3657ab84d7
-- title:
--   Proof of Theorem 1, "if" half: $R'\in\operatorname{conv}\mathcal R$, $R'\le c\cdot\mathbf e$ give $R^\star(p)\le p^\top R'\le c$ for every $p\in\Delta(\mathcal S)$
-- statement:
--   Let $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$ be a robust assortment instance satisfying the standing assumptions of §3, with $\mathcal U$ a compact subset of a finite-dimensional real normed space. Let $\mathcal R$ be its set of expected revenue vectors, $c$ a real number, and $R'\in\operatorname{conv}\mathcal R$ with $R'\le c\cdot\mathbf e$ componentwise. Then every randomized assortment $p\in\Delta(\mathcal S)$ satisfies
--   $$
--   R^\star(p)\le p^\top R'\le c .
--   $$
--
--   With $c=R^\star_{\mathrm{det}}(\mathcal U)$ and the maximum over $p$, this gives $R^\star_{\mathrm{rand}}(\mathcal U)\le R^\star_{\mathrm{det}}(\mathcal U)$, which is the "if" half of Theorem 1.
--
--   **Formalization Note** $R^\star(p)$ is the real infimum of $R(p,u)$ over $u\in\mathcal U$, and $p^\top R'=\sum_{S\in\mathcal S}p_SR'_S$. No continuity of $u\mapsto R(S,u)$ is assumed.
--
--   Differences from the source:
--   - generalization: threshold R⋆_det(𝒰) → an arbitrary real c; reason: the statement at c = R⋆_det(𝒰) is the source's
--   - reading: chain R⋆(p) = min_{R∈conv ℛ} p⊤R ≤ p⊤R′, whose identity is quoted from (5) → R⋆(p) ≤ p⊤R′; reason: the identity is e-companion eq. (5), a separate milestone that states the attainment; this step uses only the inequality it gives for R′ ∈ conv ℛ, which holds for the infimum without lower semicontinuity
--   - encoding: products {1,…,n}, alternatives 𝒩₀ = 𝒩 ∪ {0} with r₀ = 0, a compact subset of a finite-dimensional space; 𝒮, 𝒰 implicitly nonempty; min over 𝒰 → Fin n, Option (Fin n) with none the no-purchase option, revenue summed over offered products, 𝒰 a subset of a finite-dimensional real normed space; 𝒮, 𝒰 nonempty in the validity predicate; R⋆(p) the real infimum ⨅; reason: Lean convention; same instances
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, proof of Theorem 1, first display, e-companion p.ec9

import Mathlib
import Definitions.Def_RandAssort_Model
import Definitions.Def_RandAssort_RevenueVectors

namespace RandAssort

/-- **Proof of Theorem 1**, first display, e-companion p.ec9 of Z. Wang, H. Peura, W. Wiesemann,
*Randomized Assortment Optimization*, Operations Research (2024), doi:10.1287/opre.2022.0129:

`R⋆(p) = min_{R ∈ conv ℛ} p⊤R ≤ p⊤R′ ≤ R⋆_det(𝒰)`.

For a valid instance, a real `c`, and a point `R′ ∈ conv ℛ` with `R′ ≤ c · e`, every randomized
assortment `p ∈ Δ(𝒮)` satisfies `R⋆(p) ≤ p⊤R′ ≤ c`; in particular its worst-case revenue is at
most `c`. The paper uses `c = R⋆_det(𝒰)`.

**Formalization Note** `R⋆(p)` is the real infimum `⨅ u ∈ 𝒰, R(p, u)` (`Instance.RstarP`) and
`p⊤R′ = ∑_{S ∈ 𝒮} p_S R′_S`. The identity `R⋆(p) = min_{R ∈ conv ℛ} p⊤R` of the display is
e-companion eq. (5), a separate statement; here only the inequality `R⋆(p) ≤ p⊤R′` it yields for
`R′ ∈ conv ℛ` is asserted, which holds without continuity of `u ↦ R(S, u)`. -/
theorem theorem_1_if_bound {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Instance n E) (hI : I.IsValid) (c : ℝ)
    (R' : I.S → ℝ) (hR' : R' ∈ convexHull ℝ I.revSet) (hle : ∀ S : I.S, R' S ≤ c)
    (p : I.S → ℝ) (hp : p ∈ stdSimplex ℝ I.S) :
    I.RstarP p ≤ ∑ S : I.S, p S * R' S ∧ ∑ S : I.S, p S * R' S ≤ c := by sorry

end RandAssort

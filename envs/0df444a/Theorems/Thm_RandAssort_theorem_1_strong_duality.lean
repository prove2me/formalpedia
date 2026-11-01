-- Prove2me | Theorems.Thm_RandAssort_theorem_1_strong_duality
-- name    : RandAssort.theorem_1_strong_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:59.467952+00:00
-- url     : https://prove2.me/theorems/b5caf0cd-6cb5-49c5-ac31-3d9fa99df0d3
-- title:
--   Proof of Theorem 1, strong duality: $\max_{p}R^\star(p)=\min_{R\in\operatorname{conv}\mathcal R}\max_{S}R_S$, both attained (corrected: lower semicontinuity added)
-- statement:
--   Let $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$ be a robust assortment instance satisfying the standing assumptions of §3, with $\mathcal U$ a compact subset of a finite-dimensional real normed space. Suppose that for every $S\in\mathcal S$ the expected revenue $u\mapsto R(S,u)$ is lower semicontinuous on $\mathcal U$. Let $\mathcal R$ be its set of expected revenue vectors. Then
--   $$
--   \max_{p\in\Delta(\mathcal S)}R^\star(p)=\max_{p\in\Delta(\mathcal S)}\min_{R\in\operatorname{conv}\mathcal R}p^\top R=\min_{R\in\operatorname{conv}\mathcal R}\max_{p\in\Delta(\mathcal S)}p^\top R=\min_{R\in\operatorname{conv}\mathcal R}\max_{S\in\mathcal S}R_S .
--   $$
--   Precisely:
--
--   1. the randomized robust value $R^\star_{\mathrm{rand}}(\mathcal U)=\max_{p\in\Delta(\mathcal S)}R^\star(p)$ is attained by some $p\in\Delta(\mathcal S)$;
--   2. $R^\star_{\mathrm{rand}}(\mathcal U)$ is the minimum, attained, of $\max_{p\in\Delta(\mathcal S)}p^\top R$ over $R\in\operatorname{conv}\mathcal R$ (strong duality);
--   3. $R^\star_{\mathrm{rand}}(\mathcal U)$ is the minimum, attained, of $\max_{S\in\mathcal S}R_S$ over $R\in\operatorname{conv}\mathcal R$.
--
--   The first equality of the display is e-companion eq. (5). This is the strong-duality step of the "only if" half of Theorem 1.
--
--   **Formalization Note** $R^\star_{\mathrm{rand}}(\mathcal U)$ is the real supremum of $R^\star(p)$ over $\Delta(\mathcal S)$. The inner maxima are real suprema over the simplex and over the finite family $\mathcal S$. `IsGreatest` and `IsLeast` assert that the values are attained.
--
--   Differences from the source:
--   - correction: no continuity of u ↦ R(S,u) (only 𝒰 compact), min over conv ℛ written as attained → u ↦ R(S,u) lower semicontinuous on 𝒰 for every S ∈ 𝒮; reason: without it the minimum over conv ℛ need not exist: n = 2, 𝒮 = {{1},{2}}, r = (2,2), 𝒰 = [0,1], (R({1},s), R({2},s)) = (1 + s², 1 − s) for s > 0 and (1, 2) at s = 0 (a valid choice model) has inf over conv ℛ of max_S R_S equal to 1, approached at (1,1) ∉ conv ℛ and not attained
--   - reading: the chain ends with '> R⋆_det(𝒰)', which 'holds by assumption' (the proof's case that no ℚ exists) → only the identities are stated; reason: the final inequality is the proof's case hypothesis, not a claim about every instance
--   - encoding: products {1,…,n}, alternatives 𝒩₀ = 𝒩 ∪ {0} with r₀ = 0, a compact subset of a finite-dimensional space → Fin n, Option (Fin n) with none the no-purchase option, revenue summed over offered products, 𝒰 a subset of a finite-dimensional real normed space; reason: Lean convention; same instances
--   - encoding: max over Δ(𝒮) and over 𝒮, min over 𝒰 and over conv ℛ; 𝒮, 𝒰 implicitly nonempty → real ⨆ and ⨅, with attainment stated by IsGreatest and IsLeast; 𝒮, 𝒰 nonempty in the validity predicate; reason: the extrema are undefined over empty sets; the suprema and infima equal the attained extrema
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, proof of Theorem 1, second display, e-companion p.ec9

import Mathlib
import Definitions.Def_RandAssort_Model
import Definitions.Def_RandAssort_RevenueVectors

namespace RandAssort

/-- **Proof of Theorem 1**, second display, e-companion p.ec9 of Z. Wang, H. Peura,
W. Wiesemann, *Randomized Assortment Optimization*, Operations Research (2024),
doi:10.1287/opre.2022.0129 (corrected: lower semicontinuity added):

`max_{p ∈ Δ(𝒮)} R⋆(p) = max_{p ∈ Δ(𝒮)} min_{R ∈ conv ℛ} p⊤R = min_{R ∈ conv ℛ} max_{p ∈ Δ(𝒮)} p⊤R
= min_{R ∈ conv ℛ} max_{S ∈ 𝒮} R_S`.

For a valid instance in which `u ↦ R(S, u)` is lower semicontinuous on `𝒰` for every `S ∈ 𝒮`:

1. `R⋆_rand(𝒰) = max_{p ∈ Δ(𝒮)} R⋆(p)` is attained by some `p ∈ Δ(𝒮)`;
2. `R⋆_rand(𝒰)` is the attained minimum over `R ∈ conv ℛ` of `max_{p ∈ Δ(𝒮)} p⊤R`
   (strong duality);
3. `R⋆_rand(𝒰)` is the attained minimum over `R ∈ conv ℛ` of `max_{S ∈ 𝒮} R_S`.

(The first identity of the display, `R⋆(p) = min_{R ∈ conv ℛ} p⊤R`, is e-companion eq. (5).)

**Formalization Note** `R⋆_rand(𝒰)` is the real supremum `⨆ p ∈ Δ(𝒮), R⋆(p)`
(`Instance.Rrand`); the inner maxima are real suprema over the simplex and over the finite family
`𝒮`. `IsGreatest`/`IsLeast` state that the values are attained. Without the lower semicontinuity
hypothesis the minimum over `conv ℛ` need not be attained. -/
theorem theorem_1_strong_duality {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Instance n E) (hI : I.IsValid)
    (hlsc : ∀ S ∈ I.S, LowerSemicontinuousOn (fun u => I.R S u) I.U) :
    IsGreatest (Set.range fun p : stdSimplex ℝ I.S => I.RstarP p) I.Rrand ∧
    IsLeast ((fun R : I.S → ℝ => ⨆ p : stdSimplex ℝ I.S, ∑ S : I.S, (p : I.S → ℝ) S * R S) ''
      convexHull ℝ I.revSet) I.Rrand ∧
    IsLeast ((fun R : I.S → ℝ => ⨆ S : I.S, R S) '' convexHull ℝ I.revSet) I.Rrand := by sorry

end RandAssort

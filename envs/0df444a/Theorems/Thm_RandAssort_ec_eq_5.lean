-- Prove2me | Theorems.Thm_RandAssort_ec_eq_5
-- name    : RandAssort.ec_eq_5
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T10:31:51.799319+00:00
-- url     : https://prove2.me/theorems/1ed3af38-c49b-4804-8248-8621e0f4bc20
-- title:
--   e-companion eq. (5): $R^\star(p)=\min_{u\in\mathcal U}R(p,u)=\min_{R\in\mathcal R}p^\top R=\min_{R\in\operatorname{conv}\mathcal R}p^\top R$ (corrected: lower semicontinuity added)
-- statement:
--   Let $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$ be a robust assortment instance satisfying the standing assumptions of §3, with $\mathcal U$ a compact subset of a finite-dimensional real normed space. Suppose that for every $S\in\mathcal S$ the expected revenue $u\mapsto R(S,u)$ is lower semicontinuous on $\mathcal U$. Let $\mathcal R$ be the set of expected revenue vectors and $\operatorname{conv}\mathcal R$ its convex hull. Then for every randomized assortment $p\in\Delta(\mathcal S)$,
--   $$
--   R^\star(p)=\min_{u\in\mathcal U}R(p,u)=\min_{R\in\mathcal R}p^\top R=\min_{R\in\operatorname{conv}\mathcal R}p^\top R,
--   $$
--   and all three minima are attained.
--
--   This identity lets the proof of Theorem 1 replace nature's choice of $u\in\mathcal U$ by a choice of $R$ in the convex set $\operatorname{conv}\mathcal R$, where a minimax theorem applies.
--
--   **Formalization Note** $R^\star(p)$ is the real infimum of $R(p,u)$ over $u\in\mathcal U$. Each of the three equalities is stated as `IsLeast`: $R^\star(p)$ belongs to the set of values and bounds it from below. Here $p^\top R=\sum_{S\in\mathcal S}p_SR_S$.
--
--   Differences from the source:
--   - correction: no continuity of u ↦ R(S,u) (only 𝒰 compact), first min written as attained → u ↦ R(S,u) lower semicontinuous on 𝒰 for every S ∈ 𝒮; reason: without it the first minimum need not exist: n = 1, 𝒮 = {{1}}, r₁ = 2, 𝒰 = [0,1], ℭ(1|{1},s) = s/2 for s ∈ (0,1] and ℭ(1|{1},0) = 1/2 satisfy every assumption, R({1},s) = s for s > 0 and R({1},0) = 1, so at p = e_{1} the infimum 0 is not attained
--   - encoding: products {1,…,n}, alternatives 𝒩₀ = 𝒩 ∪ {0} with r₀ = 0, a compact subset of a finite-dimensional space → Fin n, Option (Fin n) with none the no-purchase option, revenue summed over offered products, 𝒰 a subset of a finite-dimensional real normed space; reason: Lean convention; same instances
--   - encoding: min over 𝒰, over ℛ, over conv ℛ; 𝒮, 𝒰 implicitly nonempty → R⋆(p) as the real infimum ⨅, each minimum stated as IsLeast (attained); 𝒮, 𝒰 nonempty in the validity predicate; reason: the minima are undefined over empty sets; the infimum equals the attained minimum
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, proof of Theorem 1, e-companion eq. (5), p.ec8

import Mathlib
import Definitions.Def_RandAssort_Model
import Definitions.Def_RandAssort_RevenueVectors

namespace RandAssort

/-- **e-companion eq. (5)**, proof of Theorem 1, e-companion p.ec8 of Z. Wang, H. Peura,
W. Wiesemann, *Randomized Assortment Optimization*, Operations Research (2024),
doi:10.1287/opre.2022.0129 (corrected: lower semicontinuity added):

`R⋆(p) = min_{u ∈ 𝒰} R(p, u) = min_{R ∈ ℛ} p⊤R = min_{R ∈ conv ℛ} p⊤R`.

For a valid instance in which `u ↦ R(S, u)` is lower semicontinuous on `𝒰` for every `S ∈ 𝒮`,
and for every randomized assortment `p ∈ Δ(𝒮)`, the worst-case revenue `R⋆(p)` is the least value
(1) of `u ↦ R(p, u)` over `𝒰`, (2) of `R ↦ p⊤R` over `ℛ`, and (3) of `R ↦ p⊤R` over the convex
hull `conv ℛ`; in particular all three minima are attained.

**Formalization Note** `R⋆(p)` is the real infimum `⨅ u ∈ 𝒰, R(p, u)` (`Instance.RstarP`);
`IsLeast A v` says that `v ∈ A` and `v` is a lower bound of `A`, i.e. `v` is the attained
minimum. `p⊤R = ∑_{S ∈ 𝒮} p_S R_S`. The paper writes `min` without a hypothesis that makes the
first minimum attained; the lower semicontinuity hypothesis is the correction (counterexample:
`n = 1`, `𝒮 = {{1}}`, `r₁ = 2`, `𝒰 = [0,1]`, `ℭ(1|{1},s) = s/2` for `s > 0` and `= 1/2` at
`s = 0`; then `inf_s R({1},s) = 0` is not attained). -/
theorem ec_eq_5 {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Instance n E) (hI : I.IsValid)
    (hlsc : ∀ S ∈ I.S, LowerSemicontinuousOn (fun u => I.R S u) I.U)
    (p : I.S → ℝ) (hp : p ∈ stdSimplex ℝ I.S) :
    IsLeast (Set.range fun u : I.U => I.Rp p u) (I.RstarP p) ∧
    IsLeast ((fun R : I.S → ℝ => ∑ S : I.S, p S * R S) '' I.revSet) (I.RstarP p) ∧
    IsLeast ((fun R : I.S → ℝ => ∑ S : I.S, p S * R S) '' convexHull ℝ I.revSet)
      (I.RstarP p) := by sorry

end RandAssort

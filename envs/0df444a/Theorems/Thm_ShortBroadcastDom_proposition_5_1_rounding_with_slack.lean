-- Prove2me | Theorems.Thm_ShortBroadcastDom_proposition_5_1_rounding_with_slack
-- name    : ShortBroadcastDom.proposition_5_1_rounding_with_slack
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:35.217601+00:00
-- url     : https://prove2.me/theorems/4cfde3a5-4f9a-45ef-9261-555187097d46
-- title:
--   Proposition 5.1 — rounding with slack
-- statement:
--   Consider a covering program whose feasible fractional solutions $x$ have cost $\mathcal C(x)$, and a rounding rule producing a set $D(x)$ from each feasible $x$.
--
--   1. If the rule has slack $\delta>0$ (that is, $\mathcal C(x)\ge(1+\delta)|D(x)|$ for every feasible $x$), then for every $\tau$, every feasible $x$ with $\mathcal C(x)\le(1+\delta)\tau$ satisfies $|D(x)|\le\tau$.
--   2. Let $S_1(x),\dots,S_k(x)\ge 0$ be quantities and $\alpha_i,\beta_i>0$ constants, $k\ge1$. If for every feasible $x$
--
--   $$
--   \mathcal C(x)-|D(x)|\ge\sum_i\alpha_iS_i(x)\qquad\text{and}\qquad|D(x)|\le\sum_i\beta_iS_i(x),
--   $$
--
--   then the rule has slack $\delta=\min_i\alpha_i/\beta_i$.
--
--   With $\tau$ the fractional optimum, part 1 says that an approximately optimal fractional solution is rounded to at most $\tau$ vertices: the rounding saving pays for the solver's error.
--
--   **Formalization Note** Feasible solutions form an abstract type, and the minimum is `Finset.inf'` over a nonempty finite index type.
--
--   Differences from the source:
--   - generalization: τ is the fractional optimum of the covering program; feasible x of that program → any real τ; an arbitrary type X of solutions with arbitrary maps 𝒞 and |D|; reason: the proof uses only the inequalities; the paper's instance is a special case
--   - encoding: S_1, …, S_k, min_i α_i/β_i → a nonempty finite index type ι and Finset.inf'; reason: the minimum over an empty family is undefined; k ≥ 1 is implicit
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §5.3, p.17 (PDF p.20), Proposition 5.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_HasSlack

namespace ShortBroadcastDom

/-- **Proposition 5.1 (Rounding with slack).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §5.3, p.17 (PDF 20): "If a rounding rule has
slack δ > 0, then every feasible x with C(x) ≤ (1 + δ)τ satisfies |D(x)| ≤ τ. Let S1(x), …, Sk(x)
be nonnegative quantities, and let αi, βi > 0 be fixed constants. If C(x) − |D(x)| ≥ ∑_i αiSi(x)
and |D(x)| ≤ ∑_i βiSi(x) for every feasible x, then the rounding rule has slack δ = min_i αi/βi."

**Formalization Note** `X` is the type of feasible solutions, `Cx = 𝒞`, `Dx = |D(·)|`. The first
part is stated for every real `τ` (the paper's `τ` is the fractional optimum), the second for a
nonempty finite index type `ι` of the quantities (`min` over an empty family is undefined), with
`min_i αᵢ/βᵢ` as `Finset.inf'`. -/
theorem proposition_5_1_rounding_with_slack {X : Type} (Cx : X → ℝ) (Dx : X → ℕ) :
    (∀ δ τ : ℝ, HasSlack Cx Dx δ → ∀ x, Cx x ≤ (1 + δ) * τ → (Dx x : ℝ) ≤ τ) ∧
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (S : ι → X → ℝ) (α β : ι → ℝ),
      (∀ i x, 0 ≤ S i x) → (∀ i, 0 < α i) → (∀ i, 0 < β i) →
      (∀ x, ∑ i, α i * S i x ≤ Cx x - Dx x) → (∀ x, (Dx x : ℝ) ≤ ∑ i, β i * S i x) →
        HasSlack Cx Dx (Finset.univ.inf' Finset.univ_nonempty fun i => α i / β i) := by sorry

end ShortBroadcastDom

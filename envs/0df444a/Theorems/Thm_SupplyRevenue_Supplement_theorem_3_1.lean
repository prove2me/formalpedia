-- Prove2me | Theorems.Thm_SupplyRevenue_Supplement_theorem_3_1
-- name    : SupplyRevenue.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:34:55.961721+00:00
-- url     : https://prove2.me/theorems/c06bc88c-73cd-4b76-ad58-ff5f6d35affe
-- title:
--   Theorem 3.1 — source-only recovery for $\mathcal S_r$: activation by $t=\min\{1,1/(2r\delta)\}$ earns $t(1-tr\delta)R$, and $(1-\varepsilon)t(1-tr\delta)R$ after query-free regularization
-- statement:
--   Let $n,m\ge 1$, let $D$ be a finite instance in $\mathcal S_r$ with $1\le r\le m$, let $\delta>0$ and let $\sigma$ be a source with aggregate caps $\delta$ and revenue $R\ge 0$. Put
--
--   $$t=\min\Bigl\{1,\frac{1}{2r\delta}\Bigr\}.$$
--
--   There are a polynomial-time regularizer and a polynomial, fixed before everything else, such that:
--
--   1. **Positive prices.** If all source prices on the assortments are positive, independent whole-offer activation of $\sigma$ by $t$ earns at least $t(1-tr\delta)R$ in every fixed order, and each buyer's actual probability of receiving each item is at most $t$ times its source marginal.
--   2. **Regularized rational prices.** If the source prices are rational and every value of every supported type is a rational with denominator at most $2^B$, then for every rational $0<\varepsilon\le 1/2$ independent whole-offer activation by $t$ of the regularized source (each offer passed through the regularizer with $m$, $B$, $\varepsilon$) earns at least $(1-\varepsilon)t(1-tr\delta)R$ in every fixed order, with the same marginal bound.
--   3. **Arithmetic.** For rational $\delta$, $t$ is a rational of polynomial bit size in the sizes of $r$ and $\delta$.
--   4. **Critical cap.** At $\delta=1/(2K)$, $K=\lceil\log_2(4m)\rceil$, the two revenues are at least $R/(2M_r)$ and, at $\varepsilon=1/2$, at least $R/(4M_r)$, where $M_r=\max\{1,r/K\}$.
--
--   No training, type or demand query, support enumeration, calibration or partition is used: a matrix costs $n$ source draws and $n$ activation coins. This is the source-only recovery behind the $\mathcal S_r$ row of Theorem 1.1.
--
--   **Formalization Note** The regularizer sees $m$, $B$, $\varepsilon$ and one offer only, and is polynomial-time on binary codes with $B$ in unary. Positive-price sources need neither $B$ nor rationality. Here $B$ is the denominator exponent, not the buy-many benchmark.
--
--   Differences from the source:
--
--   - encoding: query-free regularization; polynomial arithmetic/price bits in m, B, log(1/ε) and sampled-price encodings → one regularizer of (m, B, ε, one offer) that is polynomial-time on binary codes with B in unary (PolyTimeRegularizer), fixed before the instance, r, δ and the residual order; reason: seeing only m, B, ε and the offer is 'query-free'; polynomial time bounds the arithmetic and the output price bits
--   - reading: polynomial arithmetic … in … cap encoding → for rational δ, t = min{1, 1/(2rδ)} is a rational of bit size ≤ c(1+x)^k at x = size r + size δ, with c, k fixed before everything; reason: the only cap-dependent arithmetic of the construction is the activation probability t
--   - encoding: a matrix uses n source draws and n activation coins; independent whole-offer activation by t → the law Mix.activate (σ i) t (resp. of the regularized source) per buyer, rows independent (indepE); reason: one source draw and one t-coin per buyer, by construction
--   - encoding: a supplied bound 2^B on supported global valuation denominators → every value of every supported type, on every bundle, is a rational with denominator ≤ 2^B; reason: literal; types of zero mass are unrestricted
--   - encoding: S_r, a supplied cap-δ source, t = min{1, 1/(2rδ)} → 1 ≤ r ≤ m, δ > 0, FeasibleSource at δ; reason: the paper's standing 1 ≤ r ≤ m (p.3); δ > 0 only excludes the case where t is undefined
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Theorem 3.1 (Source-only recovery for complements), p.7

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Supplement_Regularizer
import Definitions.Def_SupplyRevenue_Supplement_Sampled

open scoped ENNReal

namespace SupplyRevenue
namespace Supplement

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Theorem 3.1 (Source-only recovery for complements), p.7.

There is a polynomial-time regularizer `reg` of `(m, B, ε, one offer)` and a polynomial `c(1+x)^k`, fixed before
everything else, such that for all
`n, m ≥ 1`, residual orders, finite instances `D` in `𝒮_r` (`1 ≤ r ≤ m`), `δ > 0` and cap-`δ` sources `σ` of revenue
`R = sourceRev ≥ 0`, with `t = min{1, 1/(2rδ)}`:
1. if all source prices on the assortments are positive, independent whole-offer activation of `σ` by `t` earns
   `≥ t(1−trδ)R` in every fixed order, and every buyer's actual allocation probability of every item is at most `t`
   times its source marginal;
2. if every value of every supported type is a rational with denominator at most `2^B` and the source prices on the
   assortments are rational, then for every rational `0 < ε ≤ 1/2` independent whole-offer activation by `t` of the
   regularized source (each atom replaced by `reg(m, B, ε, atom)`) earns `≥ (1−ε)t(1−trδ)R` in every order, with the
   same marginal bound;
3. for rational `δ` the activation probability `t` is a rational whose bit size is at most a fixed polynomial
   `c(1+x)^k` of the sizes of `r` and `δ` (the "cap" part of the arithmetic clause);
4. at the critical cap `δ = 1/(2K)`, `K = ⌈log₂(4m)⌉`, the two revenues are `≥ R/(2M_r)` and, at `ε = 1/2`, `≥ R/(4M_r)`.

**Formalization Note** Activation is `Mix.activate` and rows are independent (`indepE`): one source draw and one
activation coin per buyer, so `n` of each. The regularizer sees `m`, `B`, `ε` and one offer only, never the instance,
`r`, `δ` or the residual order; it is polynomial-time on binary codes with `B` in unary (`PolyTimeRegularizer`), which
bounds its arithmetic and output price bits. `t` is the activation probability; for rational `δ` it is the rational
`min{1, 1/(2rδ)}`. Positive-price sources need no `B` and no rationality. `B` here is the denominator exponent, not the
buy-many benchmark. -/
theorem theorem_3_1 :
    ∃ reg : RegInput → List ℚ, PolyTimeRegularizer reg ∧ ∃ c k : ℕ,
      ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m) (r : ℕ), 1 ≤ r → r ≤ m →
        InstanceInClass D (InS r) → ∀ (δ : ℝ), 0 < δ → ∀ σ : Source n m, FeasibleSource tie D δ σ →
        let t : ℝ := min 1 (1 / (2 * (r : ℝ) * δ))
        let R : ℝ := sourceRev tie D σ
        let posLaw : Fin n → Mix (Offer m) := fun i => (σ i).activate t
        let regLaw : ℕ → ℚ → Fin n → Mix (Offer m) := fun B ε i =>
          ((σ i).map fun _ o => regOffer reg m B ε o).activate t
        let Positive : Prop := ∀ i a, ∀ j ∈ ((σ i).atom a).assort, 0 < ((σ i).atom a).price j
        let RationalPrices : Prop := ∀ i a, ∀ j ∈ ((σ i).atom a).assort, ∃ q : ℚ, ((σ i).atom a).price j = q
        let DenBound : ℕ → Prop := fun B => ∀ i θ, 0 < (D i).mass θ → ∀ T : Finset (Fin m),
          ∃ q : ℚ, (D i).val θ T = q ∧ q.den ≤ 2 ^ B
        (∀ δq : ℚ, δ = δq → ∃ tq : ℚ, (tq : ℝ) = t ∧ sizeQ tq ≤ poly c k (Nat.size r + sizeQ δq)) ∧
        (Positive → ∀ π : Equiv.Perm (Fin n),
          t * (1 - t * (r : ℝ) * δ) * R ≤ indepE posLaw (fun P => rev tie D P π) ∧
          ∀ i j, indepE posLaw (fun P => allocProb tie D P π i j) ≤ t * sourceMarginal tie (D i) (σ i) j) ∧
        (∀ B : ℕ, DenBound B → RationalPrices → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∀ π : Equiv.Perm (Fin n),
          (1 - (ε : ℝ)) * t * (1 - t * (r : ℝ) * δ) * R ≤ indepE (regLaw B ε) (fun P => rev tie D P π) ∧
          ∀ i j, indepE (regLaw B ε) (fun P => allocProb tie D P π i j) ≤
            t * sourceMarginal tie (D i) (σ i) j) ∧
        (δ = 1 / (2 * (capK m : ℝ)) →
          (Positive → ∀ π : Equiv.Perm (Fin n),
            R / (2 * Mr m r) ≤ indepE posLaw (fun P => rev tie D P π)) ∧
          (∀ B : ℕ, DenBound B → RationalPrices → ∀ π : Equiv.Perm (Fin n),
            R / (4 * Mr m r) ≤ indepE (regLaw B (1 / 2)) (fun P => rev tie D P π))) := by sorry

end Supplement
end SupplyRevenue

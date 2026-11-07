-- Prove2me | Theorems.Thm_SupplyRevenue_theorem_1_1
-- name    : SupplyRevenue.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:30.863197+00:00
-- url     : https://prove2.me/theorems/779f77a6-755f-4837-8f8e-a9c1b0ee5450
-- title:
--   Theorem 1.1 — sharp supply-sensitive comparisons for XOS, $\mathcal V_d$ and $\mathcal S_r$
-- statement:
--   For independent finite real buyers, every residual order, $0<\delta\le 1$, $1\le d,r\le m$, $K=\lceil\log_2(4m)\rceil$ and $M_r=\max\{1,r/K\}$, with $\mathrm{Obl}=\mathrm{OblivItemRev}$:
--
--   $$\begin{array}{c|ccc}\text{class} & A_\delta\le & A_{1/(2K)}\le & B\le\\ \hline \text{XOS} & 192(1+\sqrt{\delta K})\,\mathrm{Obl} & 48\,\mathrm{Obl} & 192K\,\mathrm{Obl}\\ \mathcal V_d & 192(1+\sqrt{\delta K}+d\delta)\,\mathrm{Obl} & 48(1+d/K)\,\mathrm{Obl} & 192(K+d)\,\mathrm{Obl}\\ \mathcal S_r & \max\{2,4r\delta\}\,\mathrm{Obl} & 2M_r\,\mathrm{Obl} & 8\max\{K,r\}\,\mathrm{Obl}\end{array}$$
--
--   These bounds are tight. There is one absolute $c>0$ such that for all $m\ge 1$, $0<\delta\le 1$, and $d,r\le\min\{m,K^2\}$, there are rational instances on $m$ items in the class, with $\mathrm{Obl}>0$ for every residual order, such that for every order $\pi$:
--
--   1. XOS: $c(1+\sqrt{\delta K})\,\mathrm{SeqItemRev}\le A_\delta$, and (another instance) $cK\,\mathrm{SeqItemRev}\le B$;
--   2. $\mathcal V_d$: $c(1+\sqrt{\delta K}+d\delta)\,\mathrm{SeqItemRev}\le A_\delta$, and $c(K+d)\,\mathrm{SeqItemRev}\le B$;
--   3. $\mathcal S_r$: $c(1+r\delta)\,\mathrm{SeqItemRev}\le A_\delta$, and $c(K+r)\,\mathrm{SeqItemRev}\le B$.
--
--   Since $\mathrm{Obl}\le\mathrm{SeqItemRev}$, this bounds the worst ratios to $\mathrm{Obl}$ as well. One price law committed before an unknown order therefore recovers the capped and buy-many benchmarks to within exactly these factors.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: a source of offers → one finite mixture of offers per buyer; reason: R4: p.2 "finite-mixture approximation"; each offer gives a point of a bounded finite-dimensional set, so arbitrary laws add nothing to the supremum
--   - reading: "adaptive closures and limits" of buy-many menus → a menu is any set of options containing the empty option, dominating every finite-depth adaptive strategy, with no closedness imposed; reason: R5: finite-depth strategies suffice for the p.6 step, and a menu dominated only in the limit has a closure in this class
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: capped single-buyer revenue $R_{BM}(D_i,x_i)$ → supremum over finite mixtures of certificates with expected inclusion marginals at most $x_i$; $x\ge 0$ in (1); reason: R7: p.2 "Sources may mix menus independently of type"
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "finite rational types", class membership → every mass and value is a rational cast; a class constrains supported types only; reason: R10: unsupported types do not affect any expectation
--   - reading: "the respective worst cap and buy-many ratios are Θ(·)" → the table, plus one absolute $c>0$ chosen before $m,\delta,d,r$, with an instance on exactly $m$ items chosen before the rank and the order, positive Obl, and the ratio against SeqItemRev; reason: R2: "apply even to adaptive randomized sequential pricing"; the chain gives the ratio to Obl; $n$ is free, as the page's families choose it
--   - reading: $\mathcal S_r$: "normalized monotone supermodular components of size at most r"; $\mathcal V_d$: "allowing either part to be zero" → each supported type has its own partition with components on subsets of each block; $g$ is normalized; reason: R11: "each type has its own unknown partition"; all values of the model are normalized
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Theorem 1.1 (Sharp supply-sensitive comparisons), p.3.

**Upper bounds**, for all `n, m ≥ 1`, all residual orders and independent finite real instances, in `ℝ≥0∞`, so that the
revenue inequalities hold literally at zero. For `0 < δ ≤ 1` and `1 ≤ d, r ≤ m`, with `K = ⌈log₂(4m)⌉`, `M_r = max{1, r/K}`:
* XOS: `A_δ ≤ 192(1 + √(δK)) Obl`, `A_{1/(2K)} ≤ 48 Obl`, `B ≤ 192K Obl`;
* `𝒱_d`: `A_δ ≤ 192(1 + √(δK) + dδ) Obl`, `A_{1/(2K)} ≤ 48(1 + d/K) Obl`, `B ≤ 192(K + d) Obl`;
* `𝒮_r`: `A_δ ≤ max{2, 4rδ} Obl`, `A_{1/(2K)} ≤ 2M_r Obl`, `B ≤ 8 max{K, r} Obl`.

**Tightness.** One absolute `c > 0` before `m, δ, d, r`, such that some rational instance on exactly `m` items, chosen
before the residual order and the buyer order, has `0 < Obl` and the matching lower bound against `SeqItemRev`, for each
of the six profiles. `d, r ≤ min{m, K²}`.

**Formalization Note** "Worst ratio is Θ" is reading R2. The bound against `SeqItemRev` (mixtures of adaptive policies, R8)
is "apply even to adaptive randomized sequential pricing", and `benchmark_chain` gives the ratio to `OblivItemRev`.
Without `0 < Obl`, an all-zero instance would satisfy every lower bound. `c` is a real, not the cost vector of §2. -/
theorem theorem_1_1 :
    (∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m),
      let K : ℝ := (capK m : ℝ)
      (InstanceInClass D IsXOS →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          capRev tie D δ ≤ ENNReal.ofReal (192 * (1 + Real.sqrt (δ * K))) * oblivRev tie D) ∧
        capRev tie D (1 / (2 * K)) ≤ ENNReal.ofReal 48 * oblivRev tie D ∧
        buyManyRev D ≤ ENNReal.ofReal (192 * K) * oblivRev tie D) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ m → InstanceInClass D (InV d) →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          capRev tie D δ ≤
            ENNReal.ofReal (192 * (1 + Real.sqrt (δ * K) + (d : ℝ) * δ)) * oblivRev tie D) ∧
        capRev tie D (1 / (2 * K)) ≤ ENNReal.ofReal (48 * (1 + (d : ℝ) / K)) * oblivRev tie D ∧
        buyManyRev D ≤ ENNReal.ofReal (192 * (K + (d : ℝ))) * oblivRev tie D) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ m → InstanceInClass D (InS r) →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          capRev tie D δ ≤ ENNReal.ofReal (max 2 (4 * (r : ℝ) * δ)) * oblivRev tie D) ∧
        capRev tie D (1 / (2 * K)) ≤ ENNReal.ofReal (2 * Mr m r) * oblivRev tie D ∧
        buyManyRev D ≤ ENNReal.ofReal (8 * max K (r : ℝ)) * oblivRev tie D)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m →
      let K : ℝ := (capK m : ℝ)
      let Witness : ((Finset (Fin m) → ℝ) → Prop) →
          (∀ {n : ℕ}, Tie m → Instance n m → Equiv.Perm (Fin n) → ENNReal → Prop) → Prop :=
        fun cls lower => ∃ (n : ℕ) (_ : 0 < n) (D : Instance n m),
          IsRationalInstance D ∧ InstanceInClass D cls ∧
            ∀ (tie : Tie m), 0 < oblivRev tie D ∧ ∀ π : Equiv.Perm (Fin n),
              lower tie D π (seqRev tie D π)
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        Witness IsXOS (fun tie D _ seq =>
          ENNReal.ofReal (c * (1 + Real.sqrt (δ * K))) * seq ≤ capRev tie D δ)) ∧
      Witness IsXOS (fun _ D _ seq => ENNReal.ofReal (c * K) * seq ≤ buyManyRev D) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ m → (d : ℝ) ≤ K ^ 2 →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          Witness (InV d) (fun tie D _ seq =>
            ENNReal.ofReal (c * (1 + Real.sqrt (δ * K) + (d : ℝ) * δ)) * seq ≤ capRev tie D δ)) ∧
        Witness (InV d) (fun _ D _ seq =>
          ENNReal.ofReal (c * (K + (d : ℝ))) * seq ≤ buyManyRev D)) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ m → (r : ℝ) ≤ K ^ 2 →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          Witness (InS r) (fun tie D _ seq =>
            ENNReal.ofReal (c * (1 + (r : ℝ) * δ)) * seq ≤ capRev tie D δ)) ∧
        Witness (InS r) (fun _ D _ seq =>
          ENNReal.ofReal (c * (K + (r : ℝ))) * seq ≤ buyManyRev D))) := by sorry

end SupplyRevenue

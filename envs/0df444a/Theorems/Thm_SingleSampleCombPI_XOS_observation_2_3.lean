-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_observation_2_3
-- name    : SingleSampleCombPI.XOS.observation_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:08:35.420196+00:00
-- url     : https://prove2.me/theorems/4808dbee-3a99-46df-8275-a44c07f55b97
-- title:
--   Observation 2.3 — free-disposal value decomposes into per-item optima
-- statement:
--   Let $b_1,\dots,b_n$ be buyer types with supporting prices $q_1,\dots,q_n$ and let $x_1,\dots,x_n\in A^m$. For item $j$ consider the single-item instance $\{(q_{i,j}(x_i),x_{i,j})\}_{i\in[n]}$.
--
--   1. For divisible items,
--   $$\mathrm{FD}(x_1,\dots,x_n)=\sum_{j=1}^m\mathrm{Opt}\big(\{(q_{i,j}(x_i),x_{i,j})\}_i\big)=\sum_{j=1}^m\mathrm{FracKnap}\big(\{(q_{i,j}(x_i),x_{i,j})\}_i\big),$$
--   where FracKnap is the optimum fractional knapsack of size $1$ with densities $q_{i,j}(x_i)$ and weights $x_{i,j}$.
--   2. For indivisible items,
--   $$\mathrm{FD}(x_1,\dots,x_n)=\sum_{j=1}^m\mathrm{Opt}\big(\{(q_{i,j}(x_i),x_{i,j})\}_i\big)=\sum_{j=1}^m\max_{i:\,x_{i,j}=1}q_{i,j}(x_i),$$
--   with the maximum of an empty family equal to $0$.
--
--   This decomposition lets the per-item single-item algorithms of the reduction act on the free-disposal value.
--
--   Differences from the source:
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: max over feasible allocations (FD, single-item Opt) → sSup of the set of attained values; reason: the sets are nonempty and bounded and the maxima are attained (finite or compact sets), so the values coincide
--   - encoding: FracKnap: items of density q_i and weight x_i, packed fractionally → sup of Σ θ_i q_i x_i over θ_i ∈ [0,1] with Σ θ_i x_i ≤ 1; reason: the standard fractional knapsack program; same value
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 9 / PDF p. 11, Observation 2.3

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Model

namespace SingleSampleCombPI.XOS

/-- **Observation 2.3** (Chawla–Dang, STOC 2027 submission #30, printed p. 9 / PDF p. 11).
For valuations with supporting prices and provisional allocations `x_i ∈ A^m`, the
free-disposal value decomposes into per-item hindsight optima: in the divisible regime these
equal the optimum fractional knapsacks of size 1 (density `q_{i,j}(x_i)`, weight `x_{i,j}`);
in the indivisible regime they equal `max_{i : x_{i,j} = 1} q_{i,j}(x_i)` (empty maximum `0`). -/
theorem observation_2_3 {n m : ℕ} (b : Fin n → Buyer m) (x : Fin n → Vec m) :
    ((∀ i, (b i).Valid .divisible) → (∀ i, InDom .divisible (x i)) →
      FD .divisible b x = ∑ j, itemOpt .divisible (itemsAt b x j) ∧
      ∑ j, itemOpt .divisible (itemsAt b x j) = ∑ j, fracKnap (itemsAt b x j)) ∧
    ((∀ i, (b i).Valid .indivisible) → (∀ i, InDom .indivisible (x i)) →
      FD .indivisible b x = ∑ j, itemOpt .indivisible (itemsAt b x j) ∧
      ∑ j, itemOpt .indivisible (itemsAt b x j) =
        ∑ j, maxOrZero (Finset.univ.filter (fun i => x i j = 1)) (fun i => (b i).q (x i) j)) := by sorry

end SingleSampleCombPI.XOS

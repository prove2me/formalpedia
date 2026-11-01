-- Prove2me | Theorems.Thm_ProactiveUpgrade_lemma_3
-- name    : ProactiveUpgrade.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:19.090163+00:00
-- url     : https://prove2.me/theorems/a18b32ff-495e-40f6-af08-f11b7844835f
-- title:
--   Lemma 3 — a stock-out of product $i$ separates the problem into two subproblems
-- statement:
--   For valid model data, $t=1,\dots,T$, any product $i$ and any inventory $x$ with $x_i=0$,
--
--   $$
--   \hat v_t(x)=\hat v_{1,t}(x_1,\dots,x_{i-1})+\hat v_{2,t}(x_{i+1},\dots,x_m),
--   $$
--
--   where $\hat v_{1,t}$ is the optimal profit function of the subproblem of products $\{1,\dots,i-1\}$ and $\hat v_{2,t}$ that of the subproblem of products $\{i,\dots,m\}$ with $x_i=0$.
--
--   Once product $i$ runs out, it is never replenished, and only one-level-up upgrades are allowed, so the two groups of products never interact.
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - generalization: product i = 2, …, m − 1 → every product i = 1, …, m; reason: at i = 1 or i = m one subproblem is empty or holds only the stocked-out product, with value 0; the statement for i = 2, …, m − 1 is a special case, and Proposition 4 states the split for every i ∈ 𝓜
--   - reading: "the remaining problem can be separated into two independent subproblems" → the identity v̂ₜ(x) = v̂_{1,t}(x₁, …, x_{i−1}) + v̂_{2,t}(x_{i+1}, …, x_m) with the subproblems' own optimal profit functions; reason: the proof (pp.36–37) and (A.3) use the lemma as this additive split
--   - reading: the subproblems of Lemma 3 and the parts v̂_{1,t}, v̂_{2,t} of (A.3), described in words only → the optimal profit functions of lowModel (products 1, …, i − 1, β₀ + Σ_{k≥i} β_k) and highModel (products i, …, m, β₀ + Σ_{k<i} β_k), the latter evaluated at x_i = 0; anti-multimodularity of each is with respect to the 𝓕 of its own dimension; reason: moving the other group's request mass to no-request is the only reading under which the groups are independent and the additive split holds; the proof of Proposition 4 (p.37) takes a, b restricted to each block, which is the block's own 𝓕
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma 3, p.24

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_subproblems

namespace ProactiveUpgrade

/-- **Lemma 3** (Chen et al., SSRN 3777846, p.24; proof pp.36–37). Whenever product `i` runs out of
stock (`xᵢ = 0`) at the beginning of period `t`, the remaining problem separates into two
independent subproblems, one for products `{1, …, i − 1}` and one for products `{i, …, m}`:
`v̂ₜ(x) = v̂_{1,t}(x₁, …, x_{i−1}) + v̂_{2,t}(x_{i+1}, …, x_m)`.

**Formalization Note** The separation is stated as this identity with the subproblems' own optimal
profit functions `lowValue`, `highValue`, for every product `i` (the paper prints
`i = 2, …, m − 1`; at `i = 1` or `i = m` one part is the empty subproblem with value `0`). -/
theorem lemma_3 {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T)
    (i : Fin m) (x : Fin m → ℕ) (hx : x i = 0) :
    vhat M T t x =
      lowValue M T i t (fun k => x (Fin.castLE i.isLt.le k)) +
        highValue M T i t (fun k => x ⟨i.val + 1 + k.val, by omega⟩) := by sorry

end ProactiveUpgrade

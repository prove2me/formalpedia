-- Prove2me | Theorems.Thm_ProactiveUpgrade_proposition_4
-- name    : ProactiveUpgrade.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:41.392455+00:00
-- url     : https://prove2.me/theorems/c76c7a2d-a227-4964-998a-1bc6264a2b09
-- title:
--   Proposition 4 — $\hat v_t$ is anti-multimodular and splits into anti-multimodular parts
-- statement:
--   For valid model data and $t=1,\dots,T$, the optimal profit function $\hat v_t$ is anti-multimodular. Furthermore, if $x_i=0$ for a product $i$ in period $t$, then
--
--   $$
--   \hat v_t(x)=\hat v_{1,t}(x_1,\dots,x_{i-1})+\hat v_{2,t}(x_{i+1},\dots,x_m),
--   $$
--
--   where $\hat v_{1,t}$ and $\hat v_{2,t}$ are also anti-multimodular (each with respect to the generator set of its own dimension).
--
--   Anti-multimodularity of the value function is what makes the optimal upgrade decision a threshold rule (Theorem 3).
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - reading: anti-multimodularity of f : ℤᵐ → ℝ, (A.1) for all x ∈ ℤᵐ (Definition A.1, p.31) → f on ℕᵐ, (A.1) whenever x, x + a, x + b, x + a + b all lie in ℕᵐ (AntiMultimodular); reason: the value functions are defined only for x ≥ 0 (p.10) and the proof of Proposition 4 treats exactly the quadrant (Case 1, p.37, excludes a, b ∈ {−e₁, d₂} at x₁ = x₂ = 0 because they leave it); this is Definition A.1 for the extension by −∞, the only extension the paper uses
--   - reading: v̂_{2,t}(x_{i+1}, …, x_n) → v̂_{2,t}(x_{i+1}, …, x_m); reason: n is not defined in the paper; the vector has the m − i coordinates after i
--   - reading: the subproblems of Lemma 3 and the parts v̂_{1,t}, v̂_{2,t} of (A.3), described in words only → the optimal profit functions of lowModel (products 1, …, i − 1, β₀ + Σ_{k≥i} β_k) and highModel (products i, …, m, β₀ + Σ_{k<i} β_k), the latter evaluated at x_i = 0; anti-multimodularity of each is with respect to the 𝓕 of its own dimension; reason: moving the other group's request mass to no-request is the only reading under which the groups are independent and the additive split holds; the proof of Proposition 4 (p.37) takes a, b restricted to each block, which is the block's own 𝓕
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proposition 4, p.24

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_AntiMultimodular
import Definitions.Def_ProactiveUpgrade_subproblems

namespace ProactiveUpgrade

/-- **Proposition 4** (Chen et al., SSRN 3777846, p.24; proof pp.37–46). For `t = 1, …, T`, the
optimal profit function `v̂ₜ(x)` in (14) is anti-multimodular. Furthermore, if `xᵢ = 0` for
`i ∈ M` in period `t`, then `v̂ₜ(x) = v̂_{1,t}(x₁, …, x_{i−1}) + v̂_{2,t}(x_{i+1}, …, x_m)`, where
`v̂_{1,t}` and `v̂_{2,t}` are also anti-multimodular.

**Formalization Note** The paper prints `x_n` for `x_m`. -/
theorem proposition_4 {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) :
    AntiMultimodular (vhat M T t) ∧
      ∀ i : Fin m,
        (∀ x : Fin m → ℕ, x i = 0 →
          vhat M T t x =
            lowValue M T i t (fun k => x (Fin.castLE i.isLt.le k)) +
              highValue M T i t (fun k => x ⟨i.val + 1 + k.val, by omega⟩)) ∧
        AntiMultimodular (lowValue M T i t) ∧ AntiMultimodular (highValue M T i t) := by sorry

end ProactiveUpgrade

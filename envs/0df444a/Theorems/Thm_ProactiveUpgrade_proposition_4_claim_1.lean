-- Prove2me | Theorems.Thm_ProactiveUpgrade_proposition_4_claim_1
-- name    : ProactiveUpgrade.proposition_4_claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:35.128449+00:00
-- url     : https://prove2.me/theorems/bc7dab9d-d2c6-44f4-b5df-e0d5f9b39e41
-- title:
--   Proof of Proposition 4, claim (1) — $\hat T_i^U$ preserves anti-multimodularity
-- statement:
--   For valid model data and $t\in\{1,\dots,T\}$, suppose $\hat v_{t+1}$ is anti-multimodular and, for every product $j$, the two parts $\hat v_{1,t+1}$, $\hat v_{2,t+1}$ of the split at $x_j=0$ are anti-multimodular. Then for every $i=1,\dots,m-1$ the function
--
--   $$
--   x\mapsto\hat T_i^U[\hat v_t(x)]
--   $$
--
--   is anti-multimodular.
--
--   This is the induction step of Proposition 4 for the controlled-upgrade operator, the nine-case core of the paper's argument.
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - reading: "the operator T̂ᵢᵁ[·] preserves anti-multimodularity" inside the induction of Proposition 4 → hypotheses: v̂_{t+1} anti-multimodular and the parts v̂_{1,t+1}, v̂_{2,t+1} of every split anti-multimodular; conclusion: x ↦ T̂ᵢᵁ[v̂ₜ(x)] anti-multimodular; reason: these are the induction hypotheses the proof states (p.37: "we suppose that v̂_{t+1}(·) is anti-multimodular such that Equation (A.3) holds for two anti-multimodular functions"); the split identity itself is Lemma 3
--   - reading: anti-multimodularity of f : ℤᵐ → ℝ, (A.1) for all x ∈ ℤᵐ (Definition A.1, p.31) → f on ℕᵐ, (A.1) whenever x, x + a, x + b, x + a + b all lie in ℕᵐ (AntiMultimodular); reason: the value functions are defined only for x ≥ 0 (p.10) and the proof of Proposition 4 treats exactly the quadrant (Case 1, p.37, excludes a, b ∈ {−e₁, d₂} at x₁ = x₂ = 0 because they leave it); this is Definition A.1 for the extension by −∞, the only extension the paper uses
--   - reading: the subproblems of Lemma 3 and the parts v̂_{1,t}, v̂_{2,t} of (A.3), described in words only → the optimal profit functions of lowModel (products 1, …, i − 1, β₀ + Σ_{k≥i} β_k) and highModel (products i, …, m, β₀ + Σ_{k<i} β_k), the latter evaluated at x_i = 0; anti-multimodularity of each is with respect to the 𝓕 of its own dimension; reason: moving the other group's request mass to no-request is the only reading under which the groups are independent and the additive split holds; the proof of Proposition 4 (p.37) takes a, b restricted to each block, which is the block's own 𝓕
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proof of Proposition 4, claim (1), pp.37–46

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_subOperators
import Definitions.Def_ProactiveUpgrade_AntiMultimodular
import Definitions.Def_ProactiveUpgrade_subproblems

namespace ProactiveUpgrade

/-- **Proof of Proposition 4, claim (1)** (Chen et al., SSRN 3777846, pp.37–46): the operator
`T̂ᵢᵁ[·]` preserves anti-multimodularity for `i = 1, …, m − 1`. Induction step: for
`t ∈ {1, …, T}`, if `v̂_{t+1}` is anti-multimodular and, for every product, the two parts
`v̂_{1,t+1}`, `v̂_{2,t+1}` of the split (A.3) are anti-multimodular, then
`x ↦ T̂ᵢᵁ[v̂ₜ(x)]` is anti-multimodular. -/
theorem proposition_4_claim_1 {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) (hv : AntiMultimodular (vhat M T (t + 1)))
    (hparts : ∀ j : Fin m, AntiMultimodular (lowValue M T j (t + 1)) ∧
      AntiMultimodular (highValue M T j (t + 1)))
    (i : Fin m) (h : i.val + 1 < m) :
    AntiMultimodular (fun x => TU M (vhat M T (t + 1)) x i h) := by sorry

end ProactiveUpgrade

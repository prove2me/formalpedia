-- Prove2me | Theorems.Thm_ProactiveUpgrade_lemma_A_5
-- name    : ProactiveUpgrade.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:31.387989+00:00
-- url     : https://prove2.me/theorems/4ce532ad-217f-4508-8813-2e42a1feede2
-- title:
--   Lemma A.5 — selling a requested unit beats keeping it: $\hat v_t(x-e_i)+p_i>\hat v_t(x)$
-- statement:
--   For valid model data, $t=1,\dots,T$ and $i=1,\dots,m$,
--
--   $$
--   \hat v_t(x-e_i)+p_i>\hat v_t(x)\qquad\text{whenever } x_i>0.
--   $$
--
--   A unit of product $i$ sold now at $p_i$ is worth strictly more than keeping it for later, because later it can at best be sold at the same price and with positive probability it is never sold.
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma A.5, p.35

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid

namespace ProactiveUpgrade

/-- **Lemma A.5** (Chen et al., SSRN 3777846, p.35; proof pp.35–36). For `t = 1, …, T` and
`i = 1, …, m`, `v̂ₜ(x − eᵢ) + pᵢ > v̂ₜ(x)` whenever `xᵢ > 0`.

**Formalization Note** Stated for any valid data; the strict inequality uses `β₀ > 0`. -/
theorem lemma_A_5 {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T)
    (i : Fin m) (x : Fin m → ℕ) (hx : 0 < x i) :
    vhat M T t x < vhat M T t (dec x i) + M.p i := by sorry

end ProactiveUpgrade

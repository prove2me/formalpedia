-- Prove2me | Theorems.Thm_ProactiveUpgrade_proposition_2
-- name    : ProactiveUpgrade.proposition_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:51:35.785549+00:00
-- url     : https://prove2.me/theorems/c3b8b618-5f36-431d-aa08-5fcae1d4109e
-- title:
--   Proposition 2 — the reformulation (14) of the optimality equation
-- statement:
--   For valid model data, every $t=1,\dots,T$ and every inventory $x$,
--
--   $$
--   \hat v_t(x)=\sum_{i=1}^{m}\lambda\beta_i\bar q_i\hat T_i^P[\hat v_t(x)]+\sum_{i=1}^{m-1}\lambda\beta_iq_i\hat T_i^U[\hat v_t(x)]+[\lambda\beta_0+(1-\lambda)]\hat v_{t+1}(x),\qquad(14)
--   $$
--
--   where $\bar q_m=1$ and $\hat T_i^P$, $\hat T_i^U$ are the parallel-fulfilment and controlled-upgrade operators.
--
--   The reformulation separates the customers who would reject an upgrade from those who would accept it, and removes $q_i$ from inside the maxima of (12); the anti-multimodularity argument works with (14).
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proposition 2, eq. (14), pp.14–15

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_subOperators

namespace ProactiveUpgrade

/-- **Proposition 2** (Chen et al., SSRN 3777846, p.14; proof pp.34–35). The optimality equation
(10) can be written as
`v̂ₜ(x) = Σ_{i=1}^{m} λβᵢq̄ᵢT̂ᵢᴾ[v̂ₜ(x)] + Σ_{i=1}^{m−1} λβᵢqᵢT̂ᵢᵁ[v̂ₜ(x)] + [λβ₀ + (1 − λ)]v̂_{t+1}(x)`
(14), with `q̄_m = 1`, for `t = 1, …, T` and every inventory `x`.

**Formalization Note** Stated for any valid data (`IsValid`), of which the MNL data are an
instance (`mnl_valid`). -/
theorem proposition_2 {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) (x : Fin m → ℕ) :
    vhat M T t x =
      ∑ i, M.lam * M.β i * qbar M i * TP M (vhat M T (t + 1)) x i +
        ∑ i, (if h : i.val + 1 < m then
          M.lam * M.β i * M.q i * TU M (vhat M T (t + 1)) x i h else 0) +
        (M.lam * M.β0 + (1 - M.lam)) * vhat M T (t + 1) x := by sorry

end ProactiveUpgrade

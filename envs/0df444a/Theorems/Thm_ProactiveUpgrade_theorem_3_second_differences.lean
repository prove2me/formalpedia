-- Prove2me | Theorems.Thm_ProactiveUpgrade_theorem_3_second_differences
-- name    : ProactiveUpgrade.theorem_3_second_differences
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:42.815824+00:00
-- url     : https://prove2.me/theorems/f73782d8-c5df-4909-9b1d-23bf2a8f03c1
-- title:
--   Proof of Theorem 3, display — $\Delta_{e_{i+1}}\Delta_{d_{i+1}}\hat v_{t+1}\ge0$ and $\Delta_{e_{i+1}}\Delta_{e_{i+1}}\hat v_{t+1}(x-e_{i+1})\le0$
-- statement:
--   For valid model data, $t=1,\dots,T$ and $i=1,\dots,m-1$,
--
--   $$
--   \Delta_{e_{i+1}}\Delta_{d_{i+1}}\hat v_{t+1}(x)\ge0\quad(x_i\ge1,\ x_{i+1}\ge1),\qquad \Delta_{e_{i+1}}\Delta_{e_{i+1}}\hat v_{t+1}(x-e_{i+1})\le0\quad(x_{i+1}\ge1).
--   $$
--
--   The first inequality says that $\hat v_{t+1}(x-e_{i+1})-\hat v_{t+1}(x-e_i)$ is nondecreasing in $x_{i+1}$, the second that $\hat v_{t+1}(x-e_{i+1})+p_i-\hat v_{t+1}(x)$ is nondecreasing in $x_{i+1}$; together they make the optimal upgrade decision a threshold rule in $x_{i+1}$.
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - reading: the two inequalities with no stated domain → asserted where every evaluated point lies in ℕᵐ: xᵢ ≥ 1 and x_{i+1} ≥ 1 for the first, x_{i+1} ≥ 1 for the second; reason: v̂ is defined only on inventories x ≥ 0; these are exactly the x at which both sides are defined
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proof of Theorem 3, p.46

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_Dir

namespace ProactiveUpgrade

/-- **Proof of Theorem 3, display** (Chen et al., SSRN 3777846, p.46). For `t = 1, …, T` and
`i = 1, …, m − 1`,
`∆_{e_{i+1}}∆_{d_{i+1}} v̂_{t+1}(x) ≥ 0` and `∆_{e_{i+1}}∆_{e_{i+1}} v̂_{t+1}(x − e_{i+1}) ≤ 0`.

**Formalization Note** Asserted at the inventories `x` where every evaluated point lies in `ℕᵐ`:
`xᵢ ≥ 1, x_{i+1} ≥ 1` for the first, `x_{i+1} ≥ 1` for the second. The index `i + 1` is
`succIdx i h`. -/
theorem theorem_3_second_differences {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ)
    (ht1 : 1 ≤ t) (htT : t ≤ T) (i : Fin m) (h : i.val + 1 < m) (x : Fin m → ℕ) :
    (0 < x i → 0 < x (succIdx i h) →
      0 ≤ (Dir.posE (succIdx i h)).delta
        ((Dir.dd (succIdx i h) (Nat.succ_pos i.val)).delta (liftZ (vhat M T (t + 1)))) (toZ x)) ∧
    (0 < x (succIdx i h) →
      (Dir.posE (succIdx i h)).delta ((Dir.posE (succIdx i h)).delta (liftZ (vhat M T (t + 1))))
        (toZ x - unitVec (succIdx i h)) ≤ 0) := by sorry

end ProactiveUpgrade

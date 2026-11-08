-- Prove2me | Theorems.Thm_ProactiveUpgrade_mnl_valid
-- name    : ProactiveUpgrade.mnl_valid
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:51:26.07358+00:00
-- url     : https://prove2.me/theorems/bebd78c9-a16b-4e05-965f-1e3c3dd08d08
-- title:
--   Eqs. (1)–(3) — the MNL data are valid, with $0<q_i<1$
-- statement:
--   Let $b>0$, let the prices satisfy $0<p_1<p_2<\dots<p_m$, let $a\in\mathbb R^m$ and $\lambda\in[0,1]$. Then the multinomial-logit probabilities $\beta_i,\beta_0$ of (1), (2) and the upgrade acceptance probabilities $q_i$ of (3) form valid model data, and
--
--   $$
--   0<q_i<1\qquad\text{for } i=1,\dots,m-1.
--   $$
--
--   This connects the paper's choice model to the abstract data on which the structural results are stated.
--
--   Differences from the source:
--   - reading: b "captures price sensitivity" (p.7), sign not stated → b > 0; reason: footnote 12 ("βᵢ is decreasing in pᵢ") and Proposition 1(1) need b > 0; at b = 0, (3) gives qᵢ = 0
--   - reading: selling prices p₁ < ⋯ < p_m (p.6) → every pᵢ > 0 and p strictly increasing; reason: prices are selling prices; Lemma A.5 at t = T needs pᵢ > 0
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, eqs. (1), (2), p.7 and (3), p.9

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_mnlModel

namespace ProactiveUpgrade

/-- **Eqs. (1)–(3) give valid data** (Chen et al., SSRN 3777846, eqs. (1), (2), p.7 and (3), p.9).
For price sensitivity `b > 0`, positive strictly increasing prices and `λ ∈ [0, 1]`, the MNL
probabilities `β, β₀` of (1), (2) and the acceptance probabilities `q` of (3) form valid model
data, and `0 < qᵢ < 1` for every `i < m`.

**Formalization Note** `b > 0` and `p > 0` are readings of the paper ("b captures price
sensitivity", footnote 12, Proposition 1; "selling prices"). -/
theorem mnl_valid {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (hb : 0 < b) (p : Fin m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hp : StrictMono p) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    IsValid (mnlModel a b p lam) ∧
      ∀ (i : Fin m), i.val + 1 < m →
        0 < (mnlModel a b p lam).q i ∧ (mnlModel a b p lam).q i < 1 := by sorry

end ProactiveUpgrade

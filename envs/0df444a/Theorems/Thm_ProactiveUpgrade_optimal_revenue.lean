-- Prove2me | Theorems.Thm_ProactiveUpgrade_optimal_revenue
-- name    : ProactiveUpgrade.optimal_revenue
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:40.319132+00:00
-- url     : https://prove2.me/theorems/e246c919-8628-4c87-af54-cddd962509fa
-- title:
--   §3.2.3 — $\hat v_t$ is the optimal revenue over proactive upgrade policies
-- statement:
--   For valid model data, $t=1,\dots,T$ and every inventory $x$:
--
--   1. no proactive upgrade policy $\pi$ collects more than $\hat v_t(x)$: $V^\pi_t(x)\le\hat v_t(x)$;
--   2. every policy that, in each period $s\in\{t,\dots,T\}$ and wherever (12) offers a choice, picks a branch attaining the maximum in (12) (with continuation value $\hat v_{s+1}$) collects exactly $\hat v_t(x)$.
--
--   This makes precise the sentence of p.12 that $\hat v_t(x)$, defined by (10), is "the optimal revenue to be collected under the optimal proactive upgrade policy from period $t$ till the end of the season".
--
--   Differences from the source:
--   - generalization: MNL data (1)–(3) with b > 0 and m ≥ 2 products → any data satisfying IsValid (0 < p₁ < ⋯ < p_m, βᵢ ≥ 0, β₀ > 0, β₀ + Σβᵢ = 1, qᵢ ∈ [0,1], λ ∈ [0,1]) and any number m of products; reason: the proofs use only these properties; MNL data satisfy them (milestone mnl_valid), and the subproblems of Lemma 3, which the induction of Proposition 4 needs, are valid data with fewer products but are not MNL data
--   - reading: "the optimal revenue to be collected under the optimal proactive upgrade policy" → v̂ₜ(x) dominates the expected revenue of every Markov proactive upgrade policy and is attained by every policy that picks maximizing branches of (12); reason: the paper never defines policies formally; its decisions depend on the period, x(t) and the request (p.8)
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §3.2.3, eq. (10), p.12

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_Policy

namespace ProactiveUpgrade

/-- **`v̂ₜ` is the optimal revenue** (Chen et al., SSRN 3777846, §3.2.3, p.12: "let v̂ₜ(x) be the
optimal revenue to be collected under the optimal proactive upgrade policy from period t till the
end of the season so that v̂ₜ(x) satisfies" (10)). For `t = 1, …, T` and every inventory `x`:
no proactive upgrade policy collects more than `v̂ₜ(x)`, and every policy that, in each period
`s ∈ {t, …, T}` and wherever (12) gives a choice, picks a branch attaining the maximum of (12)
collects exactly `v̂ₜ(x)`. -/
theorem optimal_revenue {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) (x : Fin m → ℕ) :
    (∀ π : Policy m, policyValue M T π t x ≤ vhat M T t x) ∧
      ∀ π : Policy m,
        (∀ (s : ℕ) (y : Fin m → ℕ) (i : Fin m) (h : i.val + 1 < m), t ≤ s → s ≤ T →
          0 < y (succIdx i h) →
          (π s y i → noOfferVal M (vhat M T (s + 1)) y i ≤ offerVal M (vhat M T (s + 1)) y i h) ∧
          (¬ π s y i → offerVal M (vhat M T (s + 1)) y i h ≤ noOfferVal M (vhat M T (s + 1)) y i)) →
        policyValue M T π t x = vhat M T t x := by sorry

end ProactiveUpgrade

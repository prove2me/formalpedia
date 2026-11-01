-- Prove2me | Theorems.Thm_ProactiveUpgrade_theorem_3
-- name    : ProactiveUpgrade.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:00.65187+00:00
-- url     : https://prove2.me/theorems/e406ca92-1057-4cd7-8e3d-cdb5b33acd85
-- title:
--   Theorem 3 — the optimal proactive upgrade policy has two thresholds $\gamma_{i,t}$, $\eta_{i,t}$
-- statement:
--   **Theorem 3 (Optimal Proactive Upgrade Policy).** Consider $m\ge2$ products with prices $0<p_1<\dots<p_m$, multinomial-logit data (1)–(3) with price sensitivity $b>0$, arrival probability $\lambda\in[0,1]$, a season of $T$ periods, a period $t\in\{1,\dots,T\}$ and an inventory $x$. Then:
--
--   1. it is always optimal to sell the highest-priced product $m$ at $p_m$ whenever a customer requests product $m$:
--   $$\hat v_{t+1}(x)\le\hat v_{t+1}(x-e_m)+p_m\qquad\text{if } x_m>0;$$
--   2. for a customer requesting product $i\in\{1,\dots,m-1\}$ with $x_i>0$, offering a free upgrade is optimal (an upgrade is possible, $x_{i+1}>0$, and the offer branch of (12) attains the maximum) if and only if $x_{i+1}\ge\gamma_{i,t}(x_{-(i+1)})$;
--   3. for a customer requesting product $i\in\{1,\dots,m-1\}$ with $x_i=0$, offering a free upgrade is optimal if and only if $x_{i+1}\ge\eta_{i,t}(x_{-(i+1)})$;
--   4. the two-threshold policy that offers exactly in these cases is optimal: its expected revenue from period $t$ is at least that of every proactive upgrade policy, and equals $\hat v_t(x)$.
--
--   The theorem says that the optimal proactive upgrade decision is governed by two state-dependent thresholds on the stock of the next product, one for when the requested product is in stock and one for when it has run out.
--
--   Differences from the source:
--   - reading: b "captures price sensitivity" (p.7), sign not stated → b > 0; reason: footnote 12 and Proposition 1(1) need b > 0; at b = 0, (3) gives qᵢ = 0, both branches of (12) coincide and the iff of clauses 1, 2 fails
--   - reading: selling prices p₁ < ⋯ < p_m (p.6) → every pᵢ > 0 and p strictly increasing; reason: prices are selling prices; Lemma A.5 at t = T needs pᵢ > 0
--   - reading: "it is always optimal to sell the highest-priced product m at p_m" → clause (a): v̂_{t+1}(x) ≤ v̂_{t+1}(x − e_m) + p_m whenever x_m > 0; reason: the sale is forced in (11), so optimality is the comparison of selling with keeping the unit
--   - reading: "it is optimal ... to offer free upgrade ... if and only if x_{i+1} ≥ γ_{i,t}" (resp. η_{i,t}) → clauses (b), (c): x_{i+1} > 0 and the offer branch of (12) is at least the no-offer branch iff x_{i+1} ≥ γ_{i,t} (resp. η_{i,t}); clause (d): the two-threshold policy is optimal over all Markov proactive upgrade policies and attains v̂ₜ(x); reason: the paper does not define policies formally; its decisions depend on the period, x(t) and the request (p.8); with (d) the theorem is about optimal decisions, not only about the recursion
--   - encoding: thresholds as minima of subsets of {1, 2, …} → sInf in ℕ∞, ⊤ on an empty set; reason: Lean convention; ⊤ means no stock level triggers an offer
--   - encoding: products 1, …, m and inventories x ∈ ℤᵐ, x ≥ 0 → Fin m (0-based, product i is index i − 1, the successor i + 1 needs i.val + 1 < m) and x : Fin m → ℕ; x − eᵢ is dec x i, used only where xᵢ > 0; reason: Lean convention; same instances
--   - encoding: periods t = 1, …, T with v̂_{T+1} = 0 → vhat M T t = valueToGo M (T + 1 − t) (periods to go), with 1 ≤ t ≤ T bound in the statement; reason: same values for 1 ≤ t ≤ T + 1
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Theorem 3, p.25 (thresholds p.24; proof p.46)

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_mnlModel
import Definitions.Def_ProactiveUpgrade_gammaThr
import Definitions.Def_ProactiveUpgrade_etaThr
import Definitions.Def_ProactiveUpgrade_Policy
import Definitions.Def_ProactiveUpgrade_thresholdPolicy

namespace ProactiveUpgrade

/-- **Theorem 3 (Optimal Proactive Upgrade Policy)** (Chen et al., SSRN 3777846, p.25; thresholds
p.24; proof p.46). Suppose the seller adopts the proactive upgrade policy. Then it is always optimal
to sell the highest-priced product `m` at `p_m` whenever a customer requests product `m`. Also, it
is optimal for the seller to offer a free upgrade to an arriving customer who requests product
`i = 1, …, m − 1` as follows: (1) if `xᵢ > 0`, offer iff `x_{i+1} ≥ γ_{i,t}(x_{−(i+1)})`; (2) if
`xᵢ = 0`, offer iff `x_{i+1} ≥ η_{i,t}(x_{−(i+1)})`.

Clauses, for MNL data with `b > 0`, positive increasing prices, `λ ∈ [0, 1]`, any `m ≥ 2`, `T`,
`t ∈ {1, …, T}` and inventory `x`:
* (a) selling product `m` is at least as good as not selling it;
* (b) for `xᵢ > 0`: offering is optimal (a choice exists and the offer branch of (12) attains the
  maximum) iff `x_{i+1} ≥ γ_{i,t}`;
* (c) for `xᵢ = 0`: the same with `η_{i,t}`;
* (d) the two-threshold policy is optimal among all proactive upgrade policies and attains `v̂ₜ(x)`.

**Formalization Note** Thresholds are in `ℕ∞` (`⊤` when the defining set is empty); policies are
Markov maps (period, inventory, request) ↦ offer or not. -/
theorem theorem_3 (m : ℕ) (hm : 2 ≤ m) (a : Fin m → ℝ) (b : ℝ) (hb : 0 < b) (p : Fin m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hp : StrictMono p) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    (∀ x : Fin m → ℕ, 0 < x ⟨m - 1, by omega⟩ →
      vhat (mnlModel a b p lam) T (t + 1) x ≤
        vhat (mnlModel a b p lam) T (t + 1) (dec x ⟨m - 1, by omega⟩) + p ⟨m - 1, by omega⟩) ∧
    (∀ (x : Fin m → ℕ) (i : Fin m) (h : i.val + 1 < m), 0 < x i →
      ((0 < x (succIdx i h) ∧
          noOfferVal (mnlModel a b p lam) (vhat (mnlModel a b p lam) T (t + 1)) x i ≤
            offerVal (mnlModel a b p lam) (vhat (mnlModel a b p lam) T (t + 1)) x i h) ↔
        gammaThr (mnlModel a b p lam) T t x i h ≤ ((x (succIdx i h) : ℕ) : ℕ∞))) ∧
    (∀ (x : Fin m → ℕ) (i : Fin m) (h : i.val + 1 < m), x i = 0 →
      ((0 < x (succIdx i h) ∧
          noOfferVal (mnlModel a b p lam) (vhat (mnlModel a b p lam) T (t + 1)) x i ≤
            offerVal (mnlModel a b p lam) (vhat (mnlModel a b p lam) T (t + 1)) x i h) ↔
        etaThr (mnlModel a b p lam) T t x i h ≤ ((x (succIdx i h) : ℕ) : ℕ∞))) ∧
    (∀ x : Fin m → ℕ,
      (∀ π : Policy m, policyValue (mnlModel a b p lam) T π t x ≤
        policyValue (mnlModel a b p lam) T (thresholdPolicy (mnlModel a b p lam) T) t x) ∧
      policyValue (mnlModel a b p lam) T (thresholdPolicy (mnlModel a b p lam) T) t x =
        vhat (mnlModel a b p lam) T t x) := by sorry

end ProactiveUpgrade

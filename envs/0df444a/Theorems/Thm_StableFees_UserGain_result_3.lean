-- Prove2me | Theorems.Thm_StableFees_UserGain_result_3
-- name    : StableFees.UserGain.result_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:24.85804+00:00
-- url     : https://prove2.me/theorems/e983dda5-f59b-4281-ae6c-314619e1bf2e
-- title:
--   Result 3, p. 16 — truthful bidding is not dominant and expected strategic gain vanishes
-- statement:
--   In the $K$-slot minimum included fee protocol, suppose $K\ge2$, bids and values lie in $[0,\bar V]$, and active values are i.i.d. from a continuous density $g$ with $g(z)\ge\epsilon>0$ on that interval. Then:
--
--   1. For every $m\ge K$ other active users, there is a valid value, alternative bid, and profile of truthful bids by the others for which the alternative bid gives strictly greater payoff than bidding one's value.
--   2. Against $m$ truthfully bidding others, the expected gain from strategic bidding, $\mathcal G_{K,\bar V}(v;m)=\sup_{b\in[0,\bar V]}\mathbb E[u_K(v,b;X)]-\mathbb E[u_K(v,v;X)]$ (the bid is chosen before the others' bids are seen), tends to zero as $m\to\infty$, uniformly over the bidder's value $v\in[0,\bar V]$. Formally, for every $\eta>0$ there is $M$ such that for all $m\ge\max\{M,K\}$ and all such $v$,
--
--   $$|\mathcal G_{K,\bar V}(v;m)|\le\eta.$$
--
--   The payoff of every admissible bid is integrable under the product value law. Together, the clauses distinguish exact dominance from vanishing incentives in large active markets.
--
--   **Formalization Note** The number $m$ counts other active users and the limit conditions on that count. The paper's total user count and participation probability are conditioned away because users choose bids knowing the active count. A bid tied at the inclusion threshold loses; ties have zero probability under the continuous density. The $K\ge2$ restriction ensures $V_{K-1}$ exists; at $K=1$ this protocol is first price.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 16, Result 3 (proof pp. 21–22)

import Mathlib
import Definitions.Def_StableFees_UserGain_Model
open MeasureTheory

namespace StableFees.UserGain

theorem result_3 (K : ℕ) (hK : 2 ≤ K) (Vbar : ℝ) (g : ℝ → ℝ) (ε : ℝ)
    (hg : ValueDensity Vbar g ε) :
    (∀ m : ℕ, K ≤ m → ∃ v ∈ Set.Icc 0 Vbar, ∃ b ∈ Set.Icc 0 Vbar,
      ∃ x : Fin m → ℝ, (∀ j, x j ∈ Set.Icc 0 Vbar) ∧
        payoff K v v x < payoff K v b x) ∧
    (∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → K ≤ m →
      ∀ v ∈ Set.Icc 0 Vbar,
        (∀ b ∈ Set.Icc 0 Vbar, Integrable (fun x : Fin m → ℝ => payoff K v b x)
          (Measure.pi fun _ : Fin m => valueLaw Vbar g)) ∧
        |expectedGain K Vbar (valueLaw Vbar g) m v| ≤ η) := by sorry

end StableFees.UserGain

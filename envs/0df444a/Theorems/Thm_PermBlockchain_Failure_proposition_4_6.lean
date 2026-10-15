-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_6
-- name    : PermBlockchain.Failure.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:27.206709+00:00
-- url     : https://prove2.me/theorems/d64ec6a3-7955-41eb-a13f-7860a9f5a61a
-- title:
--   Proposition 4.6, p. 18 — global welfare: adoption helps for large Δ, hurts for large adoption costs
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions, with $L$ fixed and $H=L+\Delta$. Write $W^X(\Delta)$ for the total welfare in scenario $X$, and say that Assumption 1 holds at $\Delta$ when $c_l'(0)<\gamma<c_l'(G(\frac{H+L+h+l}2-\gamma))$.
--
--   1. **Full adoption can raise welfare.** There is $\underline\Delta$ such that $W^F(\Delta)>W^N(\Delta)$ for every $\Delta>\underline\Delta$ at which Assumption 1 holds.
--   2. **Partial adoption can raise welfare.** There is $\underline\Delta$ such that $W^P(\Delta)>W^N(\Delta)$ for every $\Delta>\underline\Delta$ at which Assumption 1 holds.
--   3. **Full adoption can lower welfare.** For every $\Delta>0$ at which Assumption 1 holds there is $\underline\chi$ such that, for every vector of positive adoption costs $(\chi_i)_{i\in M}$ with $\sum_{i\in M}\chi_i>\underline\chi$, $W^F(\Delta)<W^N(\Delta)$ in the model with these costs.
--   4. **Partial adoption can lower welfare.** For every $\Delta>0$ at which Assumption 1 holds there is $\underline\chi$ such that, for every vector of positive adoption costs with $\sum_{i:\xi_i=h}\chi_i>\underline\chi$, $W^P(\Delta)<W^N(\Delta)$ in the model with these costs.
--
--   In formulas, item 1 reads
--   $$\exists\,\underline\Delta\ \ \forall\,\Delta>\underline\Delta:\quad W^F(\Delta)>W^N(\Delta).$$
--
--   Blockchain adoption thus has ambiguous effects on global welfare: the consumer gain grows with $\Delta$, while the manufacturer loss grows with the adoption costs.
--
--   **Formalization Note** In items 3–4 only the adoption costs change (the model `M.withχ χ'`); $\Delta$ and all other parameters are fixed first, as in the proof on p. 35. Assumption 1 depends on $\Delta$ through $H$, so it is a hypothesis at each $\Delta$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 18, Proposition 4.6

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

/-- **Proposition 4.6** (p. 18), all four bullets: with `Δ = H − L` and `L` fixed,
1. `W^F > W^N` for all sufficiently large `Δ`;
2. `W^P > W^N` for all sufficiently large `Δ`;
3. at fixed `Δ`, `W^F < W^N` once `Σ_{i ∈ M} χ_i` is large enough;
4. at fixed `Δ`, `W^P < W^N` once `Σ_{i : ξ_i = h} χ_i` is large enough. -/
theorem proposition_4_6 {m : ℕ} (M : Model m) (hM : M.Standing) :
    (∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.W .N Δ < M.W .F Δ) ∧
    (∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.W .N Δ < M.W .P Δ) ∧
    (∀ Δ : ℝ, 0 < Δ → M.Assumption1 Δ → ∃ χ₀ : ℝ, ∀ χ' : Mfr m → ℝ, (∀ i, 0 < χ' i) →
      χ₀ < ∑ i, χ' i → (M.withχ χ').W .F Δ < (M.withχ χ').W .N Δ) ∧
    (∀ Δ : ℝ, 0 < Δ → M.Assumption1 Δ → ∃ χ₀ : ℝ, ∀ χ' : Mfr m → ℝ, (∀ i, 0 < χ' i) →
      χ₀ < ∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), χ' i →
      (M.withχ χ').W .P Δ < (M.withχ χ').W .N Δ) := by sorry

end PermBlockchain.Failure

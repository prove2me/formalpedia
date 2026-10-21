-- Prove2me | Theorems.Thm_TechFinConstr_Selection_proposition_1
-- name    : TechFinConstr.Selection.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:12.694308+00:00
-- url     : https://prove2.me/theorems/8b54fa1b-2e81-4406-9b0c-902b2d550ca8
-- title:
--   Proposition 1, p. 11 — the greedy tranche contract with weights λ is optimal; 0 = c̄₀ < c̄₁ ≤ ⋯ ≤ c̄ₙ = π
-- statement:
--   In Starmans' model, let $p\in\mathscr P$ and let $\sigma$ be a permutation of the tranche indices $\{1,\dots,n\}$ ordering the cumulative likelihood ratios decreasingly, $\Phi_{\sigma(1)}(p)\ge\Phi_{\sigma(2)}(p)\ge\dots\ge\Phi_{\sigma(n)}(p)$. For $k\in\{0,\dots,n\}$ put
--   $$\bar c_k=\sum_{j=1}^k\bigl(x_{\sigma(j)}-x_{\sigma(j)-1}\bigr)\,\Phi_{\sigma(j)}(p)\sum_{i=\sigma(j)}^n q_i .$$
--   Then
--
--   1. $0=\bar c_0<\bar c_1\le\bar c_2\le\dots\le\bar c_n=\pi$;
--   2. for every $m\in\{1,\dots,n\}$ and every disutility of effort $c$ with $\bar c_{m-1}<c\le\bar c_m$, the weight $\lambda_{\sigma(m)}=(c-\bar c_{m-1})/(\bar c_m-\bar c_{m-1})$ lies in $(0,1]$, and the contract
--   $$s^*(p)=\sum_{j=1}^{m-1}\bar s^{\sigma(j)}+\lambda_{\sigma(m)}\,\bar s^{\sigma(m)}$$
--   is an optimal contract of problem (1), i.e. it satisfies (1b)–(1f) and maximizes $\mathbb E_p[x-s]$ among all contracts that do.
--
--   The proposition solves the contracting problem in closed form: the investor fills the most informative tranches first. It is the basis of the agency-rent formula (Proposition 2).
--
--   **Formalization Note.** `σ : Equiv.Perm (Fin n)` maps positions to tranches: position `j` (the paper's $j+1$) holds tranche `σ j` (the paper's $\sigma(j+1)$), and `m : Fin n` is the paper's $m-1$. The page also writes "$\ge0$" after $\Phi_{\sigma(n)}(p)$; this holds for every $p\in\mathscr P$ (p. 11) and is not a hypothesis. $\bar c_0=0$ holds by definition (empty sum).
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 11, Proposition 1 (proof pp. 34–38, Appendix A.1)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

open Finset

theorem proposition_1 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ a b : Fin n, a ≤ b → Phi E p (σ b).succ ≤ Phi E p (σ a).succ) :
    0 < cbar E p σ 1 ∧
    (∀ k : ℕ, 1 ≤ k → k < n → cbar E p σ k ≤ cbar E p σ (k + 1)) ∧
    cbar E p σ n = E.piE ∧
    ∀ (m : Fin n) (c : ℝ), cbar E p σ m.val < c → c ≤ cbar E p σ (m.val + 1) →
      0 < (c - cbar E p σ m.val) / (cbar E p σ (m.val + 1) - cbar E p σ m.val) ∧
      (c - cbar E p σ m.val) / (cbar E p σ (m.val + 1) - cbar E p σ m.val) ≤ 1 ∧
      IsOptimalContract E p c (fun i =>
        ∑ j ∈ univ.filter (fun j : Fin n => j.val < m.val), tranche E (σ j) i +
          (c - cbar E p σ m.val) / (cbar E p σ (m.val + 1) - cbar E p σ m.val) *
            tranche E (σ m) i) := by sorry

end TechFinConstr.Selection

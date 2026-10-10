-- Prove2me | Theorems.Thm_SDDiP_Conv_finite_changes
-- name    : SDDiP.Conv.finite_changes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:47:22.301269+00:00
-- url     : https://prove2.me/theorems/21163fe9-c70c-4d93-a887-6d33c3717ca8
-- title:
--   Proof of Theorem 2 — with finitely many possible cuts, the approximations $\{\psi^i_n\}$ change only finitely often
-- statement:
--   Consider a run of the SND algorithm in which every cut generated in the backward steps belongs to one finite set $C\subseteq\mathbb R\times\mathbb R^d$. Then the approximate expected cost-to-go functions change in only finitely many iterations: there is an iteration $i_1$ such that
--   $$\psi^i_n = \psi^{i_1}_n \quad\text{on } \{0,1\}^d\qquad\text{for all } n\in\mathcal T \text{ and all } i\ge i_1 .$$
--
--   In the proof of Theorem 2 this is the statement that there are finitely many possible polyhedral models $\{\psi^i_n\}_{n\in\mathcal T}$ and that the Type-a iterations (those in which some $\psi^i_n$ changes) are finite in number.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), pp. 474–475, proof of Theorem 2

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage

/-- Proof of Theorem 2, pp. 474–475 (Zou–Ahmed–Sun 2019): if all cuts generated along the run lie in
one finite set, the approximate expected cost-to-go functions `{ψ^i_n}_{n ∈ T}` change in only
finitely many iterations: from some iteration `i₁` on they are all equal to `{ψ^{i₁}_n}_{n ∈ T}`. -/
theorem finite_changes {H d ℓ M : ℕ} (D : Model H d ℓ) (L : D.T.Node → ℝ)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hfin : D.FiniteCuts s κ) :
    ∃ i₁, ∀ i ≥ i₁, D.approx L s κ i = D.approx L s κ i₁ := by sorry

end SDDiP.Conv

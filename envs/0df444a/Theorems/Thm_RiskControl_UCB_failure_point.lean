-- Prove2me | Theorems.Thm_RiskControl_UCB_failure_point
-- name    : RiskControl.UCB.failure_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:51.127648+00:00
-- url     : https://prove2.me/theorems/e2fda4a2-8b5a-42bf-832b-07d586dce057
-- title:
--   Proof of Theorem A.1, p. 26 (corrected) — λ† = sup{λ ∈ Λ : R(λ) > α} lies in Λ and R(λ†) ≥ α
-- statement:
--   Let $\Lambda \subseteq \overline{\mathbb R} = \mathbb R \cup \{\pm\infty\}$ be closed, let $R : \overline{\mathbb R} \to \mathbb R$ be continuous on $\Lambda$, and let $\alpha \in \mathbb R$. Suppose some $\lambda \in \Lambda$ has $R(\lambda) > \alpha$, and set
--   $$\lambda^\dagger = \sup\{\lambda \in \Lambda : R(\lambda) > \alpha\}.$$
--   Then
--   $$\lambda^\dagger \in \Lambda \quad\text{and}\quad R(\lambda^\dagger) \ge \alpha.$$
--
--   The point $\lambda^\dagger$ is the deterministic place where a failure of UCB calibration is detected: it depends only on $R$ and $\alpha$, not on the data, so the pointwise confidence bound (3) can be applied at it.
--
--   **Formalization Note** This replaces a step of the printed proof of Theorem A.1, which introduces $\lambda^* = \inf\{\lambda \in \Lambda : R(\lambda) \le \alpha\}$ and asserts $R(\lambda^*) = \alpha$ "by continuity". That assertion fails when $\Lambda$ is not an interval: for $\Lambda = \{0, 1\}$, $R(0) = 1$, $R(1) = 0$, $\alpha = 1/2$ one gets $\lambda^* = 1$ and $R(\lambda^*) = 0$. The corrected point $\lambda^\dagger$ coincides with $\lambda^*$ when $\Lambda$ is an interval. No monotonicity of $R$ is assumed. The supremum is taken in the extended reals, and continuity is with respect to the subspace topology of $\Lambda$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem A.1, p. 26 (the point λ* and 'R(λ*) = α (by continuity)'), corrected to λ† = sup{λ ∈ Λ : R(λ) > α}

import Mathlib

namespace RiskControl.UCB

/-- Proof of Theorem A.1, p. 26, corrected: for a closed `Λ ⊆ EReal` and a function `R`
continuous on `Λ`, if some `λ ∈ Λ` has `R(λ) > α`, then `λ† = sup {λ ∈ Λ : R(λ) > α}` lies in
`Λ` and `R(λ†) ≥ α`. (The page uses `λ* = inf {λ ∈ Λ : R(λ) ≤ α}` with `R(λ*) = α`, which fails
when `Λ` is not an interval.) -/
theorem failure_point (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (α : ℝ) (hU : {l ∈ Λ | α < R l}.Nonempty) :
    sSup {l ∈ Λ | α < R l} ∈ Λ ∧ α ≤ R (sSup {l ∈ Λ | α < R l}) := by sorry

end RiskControl.UCB

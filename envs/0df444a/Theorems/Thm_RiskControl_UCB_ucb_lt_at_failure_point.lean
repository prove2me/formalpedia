-- Prove2me | Theorems.Thm_RiskControl_UCB_ucb_lt_at_failure_point
-- name    : RiskControl.UCB.ucb_lt_at_failure_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:37.892628+00:00
-- url     : https://prove2.me/theorems/9cbe5a19-63dd-4106-8cba-f326c067b8ac
-- title:
--   Proof of Theorem A.1, p. 26 (corrected) — if R(λ̂) > α then R̂⁺(λ†) < α at λ† = sup{λ ∈ Λ : R(λ) > α}
-- statement:
--   Let $\Lambda \subseteq \overline{\mathbb R}$ be closed, let $R : \overline{\mathbb R} \to \mathbb R$ be continuous on $\Lambda$, let $\alpha \in \mathbb R$, and let $r : \overline{\mathbb R} \to \mathbb R$ be any function (one realization of the upper confidence bound $\widehat R^+$). Let
--   $$\hat\lambda = \inf\{\lambda \in \Lambda : r(\lambda') < \alpha \text{ for all } \lambda' \in \Lambda,\ \lambda' \ge \lambda\}$$
--   as in (4). If this calibration set is nonempty and $R(\hat\lambda) > \alpha$, then the set $\{\lambda \in \Lambda : R(\lambda) > \alpha\}$ is nonempty and, with $\lambda^\dagger = \sup\{\lambda \in \Lambda : R(\lambda) > \alpha\}$,
--   $$r(\lambda^\dagger) < \alpha.$$
--
--   This is a purely deterministic statement: whenever UCB calibration selects a parameter with risk above $\alpha$, the upper confidence bound is already below $\alpha$ at the fixed point $\lambda^\dagger$. Together with $R(\lambda^\dagger) \ge \alpha$, the failure of calibration is contained in the failure of the pointwise bound (3) at $\lambda^\dagger$.
--
--   **Formalization Note** The printed proof argues "$\hat\lambda < \lambda^*$" and then "$\widehat R^+(\lambda^*) < \alpha$" with $\lambda^* = \inf\{\lambda \in \Lambda : R(\lambda) \le \alpha\}$; that route needs $R(\lambda^*) = \alpha$, false for non-interval $\Lambda$ (see the failure-point milestone). This statement uses $\lambda^\dagger$ instead. No monotonicity of $R$ is assumed.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem A.1, p. 26, second and third sentences, corrected (λ† for λ*)

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting

namespace RiskControl.UCB

/-- Proof of Theorem A.1, p. 26, corrected: deterministically, for one realization `r` of
`λ ↦ R̂⁺(λ)`, if the calibration set of (4) is nonempty and `R(λ̂) > α`, then the set
`{λ ∈ Λ : R(λ) > α}` is nonempty and `R̂⁺(λ†) < α` at its supremum `λ†`. -/
theorem ucb_lt_at_failure_point (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (r : EReal → ℝ) (α : ℝ)
    (hS : (calSet Λ r α).Nonempty) (hfail : α < R (lambdaHat Λ r α)) :
    {l ∈ Λ | α < R l}.Nonempty ∧ r (sSup {l ∈ Λ | α < R l}) < α := by sorry

end RiskControl.UCB

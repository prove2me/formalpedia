-- Prove2me | Theorems.Thm_StableDispatch_Markov_theorem_2_1
-- name    : StableDispatch.Markov.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:18.876292+00:00
-- url     : https://prove2.me/theorems/196c8812-5e66-4b40-9603-bad905dfda95
-- title:
--   Theorem 2.1, p. 6 — the single-ID dispatching policy is stable for every rate vector in Σ_n
-- statement:
--   Consider $n$ parallel servers with service rates $\mu\in\Sigma_n=\{\mu\in(0,\infty)^n:\sum_i\mu_i=n\}$, Poisson arrivals of rate $\lambda n$ and i.i.d. exponential job sizes of unit mean. The dispatcher remembers the ID of one server and sends every arriving job to it; each server reports its queue length as a Poisson process of rate $\alpha_n$, and the dispatcher switches to the sender exactly when the sender's queue is strictly shorter than the stored server's. The system is the continuous-time Markov chain $(Q(\cdot),I(\cdot))$ of queue lengths and stored ID.
--
--   **Theorem 2.1.** For any $n$, if $\alpha_n>0$, then for all $\lambda\in(0,1)$ the stability region of this policy is all of $\Sigma_n$:
--   $$\Gamma_n(\lambda)=\{\mu\in\Sigma_n:\ (Q(\cdot),I(\cdot))\text{ is positive recurrent}\}=\Sigma_n .$$
--
--   So one remembered server ID ($\lceil\log_2 n\rceil$ bits of memory) and an arbitrarily small positive message rate suffice for a policy that is stable for every admissible vector of server rates, even though the rates are unknown to the dispatcher.
--
--   **Formalization Note.** "Positive recurrent" is the published `MatrixAnalytic.Tree.IsPositiveRecurrentProcess` of the generator: every state is recurrent and has a finite expected return time. The Poisson/exponential assumptions are built into the generator.
--
--   Differences from the source:
--   - reading: stability region Γ_n(λ) = rates for which (Q(·), M(·), Z(·)) is positive Harris recurrent (§2.4) → rates for which the CTMC (Q(·), I(·)) is positive recurrent (IsPositiveRecurrentProcess of gen); reason: §2.2.2 states Theorem 2.1 "in this setting" of the CTMC (Q, I), and the proof concludes from its positive recurrence that Σ_n is the stability region
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 6, Theorem 2.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem theorem_2_1 (n : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → stabilityRegion n lam α = Sigma n := by sorry

end StableDispatch.Markov

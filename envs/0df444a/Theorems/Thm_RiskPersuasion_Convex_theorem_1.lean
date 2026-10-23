-- Prove2me | Theorems.Thm_RiskPersuasion_Convex_theorem_1
-- name    : RiskPersuasion.Convex.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:05.851179+00:00
-- url     : https://prove2.me/theorems/249712d1-2936-41fe-9ec5-b37b11e13420
-- title:
--   Theorem 1 — the sender's persuasion problem (3) is solved by the convex program (7)
-- statement:
--   Let $\Omega$ be a finite state space with prior $\mu^* \in \Delta(\Omega)$, $A$ a nonempty finite action set, $\rho : \Delta(\Omega) \times A \to \mathbb{R}$ the receiver's (risk-conscious) utility, and $v : \Omega \times A \to \mathbb{R}$ the sender's utility. Assume every set $P_a = \{\mu \in \Delta(\Omega) : a \in \arg\max_{a'} \rho(\mu, a')\}$ is closed (Assumption 1).
--
--   Then the set of sender values achievable in the persuasion problem (3), that is, all $\mathbb{E}_\pi[v(\bar\omega, a(\bar s))]$ over signal spaces $S$, signaling schemes $\pi$ on $\Omega \times S$ with $\Omega$-marginal $\mu^*$, versions of the Bayes posterior $\mu_s$, and measurable optimal receiver strategies $a(\cdot)$ with $a(s) \in \arg\max_{a} \rho(\mu_s, a)$, is exactly the set of objective values of the convex program
--   $$\max_{\{t_a : a \in A\}} \sum_{\omega \in \Omega} \sum_{a \in A} t_a(\omega)\, v(\omega,a) \quad \text{s.t.} \quad \sum_{a \in A} t_a(\omega) = \mu^*(\omega)\ \ (\omega \in \Omega), \qquad t_a \in \operatorname{Conv}(P_a \cup \{0\})\ \ (a \in A). \qquad (7)$$
--   over its feasible points.
--
--   Equivalently: every signaling scheme with an optimal receiver response yields a feasible $t$ of (7) with the same value (namely $t_a(\omega) = \pi(\bar\omega = \omega,\ a(\bar s) = a)$), and every feasible $t$ is realized by some signaling scheme. Hence the supremum of (3) is the maximum of (7), and an optimal solution of (7) yields an optimal signaling scheme; this is the sense of "can be optimized by solving".
--
--   **Formalization Note** Signal spaces range over all measurable types; posteriors are versions of Bayes' rule valued in the simplex; strategies are measurable. The statement is a set equality, not an equality of suprema, so it carries both directions of the reformulation.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 17, Theorem 1, program (7) (proof p. 38); Assumption 1, p. 13

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Program7

open MeasureTheory

namespace RiskPersuasion.Convex

theorem theorem_1 {Ω A : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Nonempty A]
    (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ)
    (hP : ∀ a : A, IsClosed (P ρ a)) :
    achievableValues μstar ρ v = objective7 v '' {t | Feasible7 μstar ρ t} := by sorry

end RiskPersuasion.Convex

-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_theorem_3
-- name    : RiskPersuasion.Binary.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:34.918556+00:00
-- url     : https://prove2.me/theorems/4a81614b-4240-45d9-943a-ee07e5714221
-- title:
--   Theorem 3 — under Assumption 2, binary persuasion program (7) is optimized by solving the linear program (10)
-- statement:
--   Consider binary persuasion: the receiver has actions $\{0,1\}$, the sender's utility satisfies $v(\omega,1)\ge v(\omega,0)$ for every state $\omega$, the prior is $\mu^*\in\Delta(\Omega)$, and the receiver's optimality regions $P_0,P_1$ are closed (Assumption 1). Suppose the non-adoption region $P_1^c=\{\mu\in\Delta(\Omega):\hat\rho(\mu)<0\}$ is convex (Assumption 2). Then the sender's convex program
--   $$\max_{t_0,t_1}\ \sum_{\omega}v(\omega,1)t_1(\omega)+v(\omega,0)t_0(\omega)\quad\text{s.t.}\quad t_a\in\operatorname{Conv}(P_a\cup\{0\}),\ t_0+t_1=\mu^* \tag{7}$$
--   can be optimized by solving the linear program
--   $$\max_{t_0,t_1}\ \sum_{\omega}v(\omega,1)t_1(\omega)+v(\omega,0)t_0(\omega)\quad\text{s.t.}\quad t_1\in\operatorname{Conv}(K_1\cup K_{01}\cup\{0\}),\ t_0\in\operatorname{Conv}(L_0\cup\{0\}),\ t_0+t_1=\mu^*. \tag{10}$$
--   Precisely:
--
--   1. every feasible solution of (10) is feasible for (7), and
--   2. for every feasible solution $t$ of (7) there is a feasible solution $t'$ of (10) whose objective value is at least that of $t$.
--
--   Since both programs have the same objective, (1) and (2) say that the two programs have the same optimal value (attained by one if and only if by the other) and that every optimal solution of (10) is an optimal solution of (7).
--
--   **Formalization Note** The paper's proof also asserts that every optimal solution of (7) is feasible for (10). That is false when $v(\omega,1)=v(\omega,0)$ for some states (for $v\equiv 0$ every feasible point of (7) is optimal); the proof's improvement steps are only weak improvements under $v(\omega,1)\ge v(\omega,0)$. The statement here is what the proof establishes; the strict-preference version is a separate item. Feasibility is stated through predicates, and the comparison through objective values, so no supremum over a possibly empty or unbounded set appears.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 24, Theorem 3 (proof pp. 40–43)

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model
import Definitions.Def_RiskPersuasion_Binary_Programs

namespace RiskPersuasion.Binary

theorem theorem_3 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (v : Ω → Fin 2 → ℝ) (μstar : Ω → ℝ)
    (hμ : μstar ∈ stdSimplex ℝ Ω) (hv : ∀ ω, v ω 0 ≤ v ω 1)
    (hA1 : Assumption1 ρ) (hA2 : Assumption2 ρ) :
    (∀ t : Fin 2 → Ω → ℝ, Feasible10 ρ μstar t → Feasible7 ρ μstar t) ∧
      (∀ t : Fin 2 → Ω → ℝ, Feasible7 ρ μstar t →
        ∃ t' : Fin 2 → Ω → ℝ, Feasible10 ρ μstar t' ∧ objective v t ≤ objective v t') := by sorry

end RiskPersuasion.Binary

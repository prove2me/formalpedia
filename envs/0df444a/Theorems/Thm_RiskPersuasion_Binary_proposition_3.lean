-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_proposition_3
-- name    : RiskPersuasion.Binary.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:18.427578+00:00
-- url     : https://prove2.me/theorems/60ebe366-0823-492a-9197-d68629a908af
-- title:
--   Proposition 3 — under monotonicity, the optimal scheme induces a threshold structure in the receiver's actions
-- statement:
--   Consider binary persuasion with prior $\mu^*\in\Delta(\Omega)$ in which the sender's gain from action $1$ is the same positive constant in every state,
--   $$v(\omega,1)-v(\omega,0)=\bar v>0\qquad\text{for all }\omega\in\Omega,$$
--   and suppose Assumptions 1 and 2 hold and $\prec$ is a strict total order on $\Omega$ satisfying Assumption 3 (monotonicity). Assume $L_0\neq\emptyset$. Let $t=(t_0,t_1)$ be an optimal solution of the linear program (10). Then there is a state $\omega_0\in L_0$ such that
--   $$t_1(\omega)=\begin{cases}\mu^*(\omega)&\text{if }\omega\prec\omega_0,\\ 0&\text{if }\omega_0\prec\omega.\end{cases}$$
--   In words: in states below the threshold $\omega_0$ the receiver always takes action $1$, and in states above it she always takes action $0$.
--
--   By Theorem 3 the optimal solutions of (10) describe optimal signaling schemes, with $t_1(\omega)$ the probability of state $\omega$ together with action $1$; the proposition says that the induced actions, not necessarily the signals, have a threshold structure.
--
--   **Formalization Note** "The optimal signaling scheme" is read as an optimal solution $t$ of (10) (feasible, with objective at least that of every feasible solution), which is what the paper's proof (p. 44) treats. The hypothesis $L_0\neq\emptyset$ is implicit in the paper: if $L_0=\emptyset$, no $\omega_0\in L_0$ exists although $t_1=\mu^*$ is optimal. The order $\prec$ is a relation given as data.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 26, Proposition 3 (Assumption 3 p. 25, proof p. 44)

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model
import Definitions.Def_RiskPersuasion_Binary_Programs

namespace RiskPersuasion.Binary

theorem proposition_3 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (v : Ω → Fin 2 → ℝ) (μstar : Ω → ℝ) (vbar : ℝ)
    (prec : Ω → Ω → Prop)
    (hμ : μstar ∈ stdSimplex ℝ Ω) (hvbar : 0 < vbar) (hv : ∀ ω, v ω 1 - v ω 0 = vbar)
    (hA1 : Assumption1 ρ) (hA2 : Assumption2 ρ) (hA3 : Assumption3 ρ prec)
    (hL0 : (L0 ρ).Nonempty)
    (t : Fin 2 → Ω → ℝ) (ht : Feasible10 ρ μstar t)
    (hopt : ∀ t' : Fin 2 → Ω → ℝ, Feasible10 ρ μstar t' → objective v t' ≤ objective v t) :
    ∃ ω₀ ∈ L0 ρ, ∀ ω : Ω, (prec ω ω₀ → t 1 ω = μstar ω) ∧ (prec ω₀ ω → t 1 ω = 0) := by sorry

end RiskPersuasion.Binary

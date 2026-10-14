-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_proposition_5_5
-- name    : ProgCorrMFG.Approx.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:41.16579+00:00
-- url     : https://prove2.me/theorems/8b16f3c0-f176-4179-a9e1-8b9990777522
-- title:
--   Proposition 5.5, p. 11 — conditional dynamic programming principle for $V_\varphi$
-- statement:
--   Assume (A1) and that $\Psi$ is measurable. Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be a correlated solution of the mean field game with initial distribution $\mathfrak m_0$ (Definition 4.3) satisfying (R1). Fix a restricted strategy $\varphi\in\mathcal R$ with $\mathbb P(\Phi=\varphi)>0$, a time $t\in[\![0,T-1]\!]$, a state history $x^{(t)}\in\mathcal X^{t+1}$ and a flow history $m^{(t)}\in\mathcal P_\varphi^{(t)}$, i.e. $\mathbb P_\varphi(\mu^{(t)}=m^{(t)})>0$. Then the conditional value function satisfies
--
--   $$V_\varphi(t,x^{(t)},m^{(t)})=\inf_{\gamma\in\Gamma}\mathbb E_\varphi\Big[f(t,x_t,m_t,\gamma)+V_\varphi\big(t+1,(x^{(t)},\Psi(t,x_t,m_t,\gamma,\xi_{t+1})),(m^{(t)},\mu_{t+1})\big)\,\Big|\,X^{(t)}=x^{(t)},\mu^{(t)}=m^{(t)}\Big],$$
--
--   where the conditional expectation is taken over $\mu_{t+1}$, distributed according to $\mathbb P_\varphi(\cdot\mid\mu^{(t)}=m^{(t)})$, and over the independent noise $\xi_{t+1}\sim\nu$.
--
--   This is the dynamic programming principle in a non-Markovian setting: the representative player conditions on the history of the flow of measures, which may be correlated with the mediator's suggestion. It is the key step of Proposition 5.6.
--
--   **Formalization Note** The paper prints $V_\varphi(t,\dots)$ inside the expectation on the right-hand side; its proof (p. 12, penultimate display) has $V_\varphi(t+1,\dots)$, which is the statement formalized. $J_\varphi$ and $V_\varphi$ are the explicit representation (5.10) (see the definition `CondValue`); the conditional expectation on the right is written in the same way, as a sum over flows $m'$ weighted by $\mathbb P_\varphi(\mu=m'\mid\mu^{(t)}=m^{(t)})$ and an integral over $z\in[0,1]$ with respect to $\nu$. Measurability of $\Psi$ is an added standing hypothesis, needed for these integrals.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 11, Proposition 5.5 (with V_φ(t+1, …) on the right, as in its proof on p. 12)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Definitions.Def_ProgCorrMFG_Approx_CondValue

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem proposition_5_5 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ)
    (φ : Strat T X G) (hφ : 0 < ρ ({φ} ×ˢ Set.univ))
    (t : Fin T) (x : Fin (T + 1) → X) (m : Flow T X)
    (hm : ∃ m' : Flow T X, (∀ s : Fin (T + 1), s ≤ t.castSucc → m' s = m s) ∧ 0 < ρ {(φ, m')}) :
    condValue M ρ φ t.castSucc x m =
      ⨅ g : G, ∑' m' : Flow T X, condFlowWeight ρ φ t.castSucc m m' *
        ∫ z, (M.f t (x t.castSucc) (m t.castSucc) g +
          condValue M ρ φ t.succ
            (Function.update x t.succ (M.Ψ t (x t.castSucc) (m t.castSucc) g z)) m')
          ∂(volume : Measure I) := by sorry

end ProgCorrMFG.Approx

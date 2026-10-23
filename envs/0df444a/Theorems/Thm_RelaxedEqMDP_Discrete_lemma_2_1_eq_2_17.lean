-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_lemma_2_1_eq_2_17
-- name    : RelaxedEqMDP.Discrete.lemma_2_1_eq_2_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:49.152266+00:00
-- url     : https://prove2.me/theorems/7c977766-65b6-4115-897d-860fbb4c8dea
-- title:
--   Lemma 2.1, (2.17), p. 8 — $\sup_i|\mathcal H(\Gamma_\lambda(y,i))|\le\kappa+\ell\ln(1+|y|)$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.2 (with constant $\Theta$) and 2.3 (with constants $\vartheta,\iota$) hold, and let $\lambda>0$. There is a constant $\kappa>0$ depending only on $\ell,\lambda,\mathrm{Leb}(U),\iota,\vartheta,\Theta$ such that
--   $$\sup_{i\in\mathcal S}\big|\mathcal H(\Gamma_\lambda(y,i))\big|\le\kappa+\ell\ln(1+|y|)\qquad\forall y\in\mathbb R^d,$$
--   where $|y|$ is the Euclidean norm.
--
--   This entropy estimate is what makes $\Psi_\lambda$ map a large ball into itself (Theorem 2.1).
--
--   **Formalization Note** The dependence of $\kappa$ is encoded by quantifier order: $\kappa$ is chosen after $\ell,\lambda,L=\mathrm{Leb}(U),\iota,\vartheta,\Theta$ and before $d$, $U$ (with $\mathrm{Leb}(U)=L$), $f$, $p$, $y$. Assumption 2.1 is not assumed, as on the page.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 8, Lemma 2.1, (2.17)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Lemma 2.1, (2.17), p. 8: under Assumptions 2.2 and 2.3,
`sup_i |ℋ(Γ_λ(y,i))| ≤ κ + ℓ ln(1 + |y|)` for all `y ∈ ℝ^d`, with `κ > 0` depending only on
`ℓ, λ, Leb(U), ι, ϑ, Θ` (it is chosen before `d, U, f, p, y`). -/
theorem lemma_2_1_eq_2_17 :
    ∀ ℓ : ℕ, 0 < ℓ → ∀ lam : ℝ, 0 < lam → ∀ L iota vartheta Theta : ℝ,
      ∃ kappa : ℝ, 0 < kappa ∧
        ∀ (d : ℕ) (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ),
          Standing U p → (volume U).toReal = L → Assumption22 U f p Theta →
            Assumption23 U iota vartheta →
              ∀ (y : Fin d → ℝ) (i : Fin d),
                |entDensity U (gibbsDensity U f p lam y i)| ≤
                  kappa + (ℓ : ℝ) * Real.log (1 + enorm2 y) := by sorry
end RelaxedEqMDP.Discrete

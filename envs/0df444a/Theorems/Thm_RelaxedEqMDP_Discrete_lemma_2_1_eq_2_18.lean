-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_lemma_2_1_eq_2_18
-- name    : RelaxedEqMDP.Discrete.lemma_2_1_eq_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:50.968284+00:00
-- url     : https://prove2.me/theorems/e21e5ef4-1385-4c85-88ed-ecf901db40c7
-- title:
--   Lemma 2.1, (2.18), p. 8 — for small $\lambda$, $\sup_i|\mathcal H(\Gamma_\lambda(y,i))|\le\kappa_1+\kappa_2|\ln\lambda|+\ell\ln(1+|y|)$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.2 (constant $\Theta$) and 2.3 (constants $\vartheta,\iota$) hold. There are constants $\kappa_1,\kappa_2>0$ and a threshold $\lambda_0>0$, depending on $\ell,\mathrm{Leb}(U),\iota,\vartheta,\Theta$ but not on $\lambda$, such that for every $\lambda\in(0,\lambda_0)$
--   $$\sup_{i\in\mathcal S}\big|\mathcal H(\Gamma_\lambda(y,i))\big|\le\kappa_1+\kappa_2|\ln\lambda|+\ell\ln(1+|y|)\qquad\forall y\in\mathbb R^d.$$
--
--   This refinement of (2.17) controls the entropy term $\lambda\,\mathcal H$ uniformly as $\lambda\downarrow0$; it drives Lemma 2.2 and the vanishing-regularization limit.
--
--   **Formalization Note** "For $\lambda>0$ small enough" is the threshold $\lambda_0$, chosen with $\kappa_1,\kappa_2$ before $\lambda$, $d$, $U$ (with $\mathrm{Leb}(U)=L$), $f$, $p$, $y$.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 8, Lemma 2.1, (2.18)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Lemma 2.1, (2.18), p. 8: under Assumptions 2.2 and 2.3, for `λ > 0` small enough,
`sup_i |ℋ(Γ_λ(y,i))| ≤ κ₁ + κ₂ |ln λ| + ℓ ln(1 + |y|)` for all `y ∈ ℝ^d`, with `κ₁, κ₂ > 0` (and the
threshold `λ₀`) depending on `ℓ, Leb(U), ι, ϑ, Θ` but not on `λ`. -/
theorem lemma_2_1_eq_2_18 :
    ∀ ℓ : ℕ, 0 < ℓ → ∀ L iota vartheta Theta : ℝ,
      ∃ kappa1 kappa2 lam0 : ℝ, 0 < kappa1 ∧ 0 < kappa2 ∧ 0 < lam0 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam0 →
        ∀ (d : ℕ) (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ),
          Standing U p → (volume U).toReal = L → Assumption22 U f p Theta →
            Assumption23 U iota vartheta →
              ∀ (y : Fin d → ℝ) (i : Fin d),
                |entDensity U (gibbsDensity U f p lam y i)| ≤
                  kappa1 + kappa2 * |Real.log lam| + (ℓ : ℝ) * Real.log (1 + enorm2 y) := by sorry
end RelaxedEqMDP.Discrete

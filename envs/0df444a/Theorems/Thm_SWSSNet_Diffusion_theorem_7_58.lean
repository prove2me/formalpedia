-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_7_58
-- name    : SWSSNet.Diffusion.theorem_7_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:53.313243+00:00
-- url     : https://prove2.me/theorems/28464553-a7f8-47ff-881a-b3bd0e786118
-- title:
--   Theorem 7, (58) — the recentred diffusion under v̄ is exponentially ergodic in the V_{ε,S}-norm with a unique invariant probability measure
-- statement:
--   Let $p$ be a positive probability vector with $\vartheta_p>0$, and let $(\hat\imath,\hat\jmath)$ be an edge. Let $B_1$ be the matrix of (38) for $\hat\jmath$. Let $S$ be positive definite and $\kappa_\circ>0$ with $SB_1+B_1^{\mathsf T}S-2\kappa_\circ I$ positive definite and $SB_1(I-e_{\hat\imath}e^{\mathsf T})+(I-ee_{\hat\imath}^{\mathsf T})B_1^{\mathsf T}S$ positive semidefinite. Assume
--   $$
--   \eta:=\vartheta_p\langle p,Se_{\hat\imath}\rangle>0 .
--   $$
--   Let $\tilde b$ be the recentred drift, i.e. (42) with $-\vartheta_pp$ in place of $h$. Let $\bar v=(e_{\hat\imath},e_{\hat\jmath})$ be the constant control (56), and $\mathcal A_{\bar v}f=\tfrac12\operatorname{trace}(\Sigma\Sigma^{\mathsf T}\nabla^2f)+\langle\tilde b(\cdot,\bar v),\nabla f\rangle$ the generator (44).
--
--   Then there is an $\varepsilon>0$ for which (57) holds (with some $\kappa_0,\kappa_1>0$, and $V_{\varepsilon,S}\in C^2$), and the following hold for the diffusion $dX_t=\tilde b(X_t,\bar v)dt+\Sigma dW_t$:
--
--   1. strong solutions exist from every initial point;
--   2. their transition probability $P^{\bar v}_t(x,\cdot)$ exists;
--   3. it has a unique invariant probability measure $\pi_{\bar v}$;
--   4. there are constants $C,\gamma>0$ with
--   $$
--   \big\|P^{\bar v}_t(x,\cdot)-\pi_{\bar v}(\cdot)\big\|_{V_{\varepsilon,S}}\le C\,V_{\varepsilon,S}(x)\,e^{-\gamma t}\qquad\forall x\in\mathbb R^I,\ t\ge0. \qquad (58)
--   $$
--
--   This is the exponential ergodicity of the stabilized limiting diffusion.
--
--   **Formalization Note** $S$ is taken from the display before Theorem 7, as in (57). The weighted norm is the published `tvNormWeighted` with weight $V_{\varepsilon,S}$: the supremum of $|\int\varphi\,d\mu_1-\int\varphi\,d\mu_2|$ over measurable $|\varphi|\le1+V_{\varepsilon,S}$, set to $\infty$ unless both measures integrate $1+V_{\varepsilon,S}$. Since $V_{\varepsilon,S}\ge1$ it lies between the paper's $V_{\varepsilon,S}$-norm and twice it, and the factor is absorbed in $C$. Existence of strong solutions is stated explicitly, so that the existence of a transition probability is not vacuous.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 26, Theorem 7, (58)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 7, (58), p. 26: under the hypotheses of (57), for an `ε > 0` for which (57) holds, the
recentred diffusion under `v̄` has strong solutions, a transition probability `P^v̄_t`, a unique
invariant probability measure `π_v̄`, and `‖P^v̄_t(x,·) − π_v̄‖_{V_{ε,S}} ≤ C V_{ε,S}(x) e^{−γt}`. -/
theorem theorem_7_58 {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p)
    (hϑ : 0 < swss N p) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ)
    (S : Matrix (Fin I) (Fin I) ℝ) (κ : ℝ) (hS : S.PosDef) (hκ : 0 < κ)
    (hSB : (S * B1 N ĵ + (B1 N ĵ)ᵀ * S - (2 * κ) • (1 : Matrix (Fin I) (Fin I) ℝ)).PosDef)
    (hΦ : (S * B1 N ĵ * (1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)))
        + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * (B1 N ĵ)ᵀ * S).PosSemidef)
    (hη : 0 < swss N p * (p ⬝ᵥ (S *ᵥ Pi.single î 1))) :
    ∃ ε : ℝ, 0 < ε ∧ ContDiff ℝ 2 (lyapVS ε S) ∧
      (∃ κ₀ κ₁ : ℝ, 0 < κ₀ ∧ 0 < κ₁ ∧ ∀ x : EthierKurtz.SDEState I,
        GPhNGIDiffusion.EMError.generator (markovDrift N (-(swss N p) • p) (fun _ => constCtrl î ĵ)) (Sigma N) (lyapVS ε S) x
          ≤ κ₀ - κ₁ * lyapVS ε S x) ∧
      HasStrongSolutions (markovDrift N (-(swss N p) • p) (fun _ => constCtrl î ĵ)) (Sigma N) ∧
      ∃ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (-(swss N p) • p) (fun _ => constCtrl î ĵ)) (Sigma N) P ∧
        ∃ π : Measure (EthierKurtz.SDEState I), GPhNGIDiffusion.EMError.IsInvariantMeasure P π ∧
          (∀ π', GPhNGIDiffusion.EMError.IsInvariantMeasure P π' → π' = π) ∧
          ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState I),
            GPhNGIDiffusion.EMError.tvNormWeighted (lyapVS ε S) (P t x) π
              ≤ ENNReal.ofReal (C * lyapVS ε S x * Real.exp (-γ * t)) := by sorry

end SWSSNet.Diffusion

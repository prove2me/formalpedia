-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_7_57
-- name    : SWSSNet.Diffusion.theorem_7_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:07.652949+00:00
-- url     : https://prove2.me/theorems/3554ece0-8324-4fe4-8a80-9c6d7e4c9356
-- title:
--   Theorem 7, (57) — under v̄ = (e_î, e_ĵ), A_v̄ V_{ε,S} ≤ κ₀ − κ₁V_{ε,S} for the recentred diffusion
-- statement:
--   Let $p$ be a positive probability vector with $\vartheta_p>0$, and let $(\hat\imath,\hat\jmath)$ be an edge. Let $B_1$ be the matrix of (38) for $\hat\jmath$. Let $S$ be positive definite and $\kappa_\circ>0$ with $SB_1+B_1^{\mathsf T}S-2\kappa_\circ I$ positive definite and $SB_1(I-e_{\hat\imath}e^{\mathsf T})+(I-ee_{\hat\imath}^{\mathsf T})B_1^{\mathsf T}S$ positive semidefinite. Assume
--   $$
--   \eta:=\vartheta_p\langle p,Se_{\hat\imath}\rangle>0 .
--   $$
--   Let $\tilde b$ be the recentred drift, i.e. (42) with $-\vartheta_pp$ in place of $h$. Let $\bar v=(e_{\hat\imath},e_{\hat\jmath})$ be the constant control (56), and $\mathcal A_{\bar v}f=\tfrac12\operatorname{trace}(\Sigma\Sigma^{\mathsf T}\nabla^2f)+\langle\tilde b(\cdot,\bar v),\nabla f\rangle$ the generator (44).
--
--   Then there are constants $\varepsilon,\kappa_0,\kappa_1>0$ such that $V_{\varepsilon,S}$ is $C^2$ and
--   $$
--   \mathcal A_{\bar v}V_{\varepsilon,S}(x)\le\kappa_0-\kappa_1V_{\varepsilon,S}(x)\qquad\forall x\in\mathbb R^I. \qquad (57)
--   $$
--
--   This Foster–Lyapunov drift inequality is the analytic core of the stability half of Theorem 1.
--
--   **Formalization Note** The paper fixes $p$ with $\eta>0$ before asserting the existence of $S$, but $\eta$ is defined from the $S$ of the preceding display. The consistent reading, used here, takes $S$ (and $\kappa_\circ$) from that display as hypotheses; the conclusion is about this $S$. The page's $x\in\mathbb R^m$ in (56) is $x\in\mathbb R^I$.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 25, Theorem 7, (57)

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

/-- Theorem 7, (57), p. 25: let `ϑ_p > 0`, `(î, ĵ)` an edge, `S` and `κ∘` as in the display before
Theorem 7, and `η = ϑ_p⟨p, Se_î⟩ > 0`. Under the constant control `v̄ = (e_î, e_ĵ)` of (56), the
recentred drift (`h = −ϑ_p p`) satisfies `A_v̄ V_{ε,S} ≤ κ₀ − κ₁ V_{ε,S}` for some `ε, κ₀, κ₁ > 0`. -/
theorem theorem_7_57 {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p)
    (hϑ : 0 < swss N p) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ)
    (S : Matrix (Fin I) (Fin I) ℝ) (κ : ℝ) (hS : S.PosDef) (hκ : 0 < κ)
    (hSB : (S * B1 N ĵ + (B1 N ĵ)ᵀ * S - (2 * κ) • (1 : Matrix (Fin I) (Fin I) ℝ)).PosDef)
    (hΦ : (S * B1 N ĵ * (1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)))
        + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * (B1 N ĵ)ᵀ * S).PosSemidef)
    (hη : 0 < swss N p * (p ⬝ᵥ (S *ᵥ Pi.single î 1))) :
    ∃ ε κ₀ κ₁ : ℝ, 0 < ε ∧ 0 < κ₀ ∧ 0 < κ₁ ∧ ContDiff ℝ 2 (lyapVS ε S) ∧
      ∀ x : EthierKurtz.SDEState I,
        GPhNGIDiffusion.EMError.generator (markovDrift N (-(swss N p) • p) (fun _ => constCtrl î ĵ)) (Sigma N) (lyapVS ε S) x
          ≤ κ₀ - κ₁ * lyapVS ε S x := by sorry

end SWSSNet.Diffusion

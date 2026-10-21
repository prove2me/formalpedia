-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_eq_dieker_gao
-- name    : SWSSNet.Diffusion.eq_dieker_gao
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:15.210038+00:00
-- url     : https://prove2.me/theorems/04283492-6ead-42f6-b411-4c8bd8ab9581
-- title:
--   p. 25 display (Dieker–Gao 2013, Prop. 3, as quoted) — S ≻ 0, κ∘ > 0 with SB₁ + B₁ᵀS > 2κ∘I and Φ ≥ 0
-- statement:
--   Let $(\hat\imath,\hat\jmath)$ be an edge and $B_1$ the matrix of (38) for the pool $\hat\jmath$. Write $e_{\hat\imath}$ for the $\hat\imath$-th unit vector and $e$ for the vector of ones. There exist a positive definite matrix $S\in\mathbb R^{I\times I}$ and a constant $\kappa_\circ>0$ such that
--   $$
--   SB_1+B_1^{\mathsf T}S-2\kappa_\circ I\ \text{ is positive definite},
--   $$
--   and
--   $$
--   \Phi:=SB_1(I-e_{\hat\imath}e^{\mathsf T})+(I-e\,e_{\hat\imath}^{\mathsf T})B_1^{\mathsf T}S\ \text{ is positive semidefinite}.
--   $$
--
--   $B_1$ and $B_1(I-e_{\hat\imath}e^{\mathsf T})$ are the linear parts of the drift under the constant control $\bar v=(e_{\hat\imath},e_{\hat\jmath})$ on the half-spaces $\langle e,x\rangle<0$ and $\langle e,x\rangle\ge0$. The matrix $S$ is a common quadratic Lyapunov matrix for the two pieces. The Lyapunov function $V_{\varepsilon,S}$ of Theorem 7 is built on it.
--
--   **Formalization Note** The paper's $e_I$ is $e_{\hat\imath}$ (class $\hat\imath$ is ordered last). The strict matrix inequality "$>2\kappa_\circ I$" is positive definiteness of the difference, and "$\ge0$" is positive semidefiniteness. The page's "$B_1^2(I-e_Ie^{\mathsf T})$" is read as $B_1(I-e_Ie^{\mathsf T})$ (a printing slip).
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 25, display before Theorem 7 (Dieker and Gao 2013, Proposition 3)

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Display before Theorem 7, p. 25 (Dieker and Gao 2013, Proposition 3, as quoted): for every edge
`(î, ĵ)` there are a positive definite `S` and `κ∘ > 0` with `SB₁ + B₁ᵀS > 2κ∘I` and
`Φ := SB₁(I − e_îeᵀ) + (I − ee_îᵀ)B₁ᵀS ≥ 0`. -/
theorem eq_dieker_gao {I J : ℕ} (N : TreeNetwork I J) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ) :
    ∃ (S : Matrix (Fin I) (Fin I) ℝ) (κ : ℝ), S.PosDef ∧ 0 < κ ∧
      (S * B1 N ĵ + (B1 N ĵ)ᵀ * S - (2 * κ) • (1 : Matrix (Fin I) (Fin I) ℝ)).PosDef ∧
      (S * B1 N ĵ * (1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)))
        + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * (B1 N ĵ)ᵀ * S).PosSemidef := by sorry

end SWSSNet.Diffusion

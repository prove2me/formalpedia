-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_lemma_1
-- name    : SunNLSDP.Equiv.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:06.851543+00:00
-- url     : https://prove2.me/theorems/174d9228-cd0b-4544-941c-c7c41992f4be
-- title:
--   Lemma 1, p. 5 — ∂_B(Ξ∘Ψ)(x̄) = ∂_BΞ(Ψ(x̄)) J_xΨ(x̄) when J_xΨ(x̄) is onto
-- statement:
--   Let $X,Y,Z$ be finite-dimensional real inner-product spaces. Let $\Psi:X\to Y$ be continuously differentiable on an open neighbourhood $\widehat N$ of $\bar x$, and let $\Xi:Y\to Z$ be locally Lipschitz continuous and directionally differentiable at every point of an open set $\mathcal O$ containing $\bar y:=\Psi(\bar x)$. If $J_x\Psi(\bar x):X\to Y$ is onto, then for $\Phi:=\Xi\circ\Psi$
--
--   $$\partial_B\Phi(\bar x)=\partial_B\Xi(\bar y)\,J_x\Psi(\bar x)=\{W\circ J_x\Psi(\bar x):W\in\partial_B\Xi(\bar y)\}.$$
--
--   Here $\partial_B$ is the B-subdifferential: the set of limits of Jacobians along sequences of differentiability points converging to the base point. The lemma is the chain rule that transfers B-subdifferentials of the projector $\Pi_{\mathcal S^p_+}$ to the KKT map.
--
--   **Formalization Note.** $\Psi$ and $\Xi$ are total functions; the hypotheses are imposed only on $\widehat N$ and $\mathcal O$, and the B-subdifferential depends only on the values near the base point.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 5, Lemma 1 (12)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem lemma_1 {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Ψ : X → Y) (Ξ : Y → Z) (xbar : X) (N : Set X) (O : Set Y)
    (hN : IsOpen N) (hxN : xbar ∈ N) (hΨ : ContDiffOn ℝ 1 Ψ N)
    (hO : IsOpen O) (hyO : Ψ xbar ∈ O)
    (hΞlip : ∀ y ∈ O, ∃ K, ∃ V ∈ 𝓝 y, LipschitzOnWith K Ξ V)
    (hΞdir : ∀ y ∈ O, ∀ v : Y, ∃ w : Z, NonsmoothNewton.Local.HasDirDerivAt Ξ y v w)
    (honto : Function.Surjective (fderiv ℝ Ψ xbar)) :
    bJac (fun x => Ξ (Ψ x)) xbar = (fun W => W.comp (fderiv ℝ Ψ xbar)) '' bJac Ξ (Ψ xbar) := by sorry
end SunNLSDP.Equiv

-- Prove2me | Theorems.Thm_StochCoordProx_lemma_4_descent
-- name    : StochCoordProx.lemma_4_descent
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:34:03.228125+00:00
-- url     : https://prove2.me/theorems/2ea11421-5afe-47ae-ab5c-c2167cf83ce3
-- title:
--   Lemma 4 — descent inequality $F(x_{k+1})\le F(x_k)-\frac{\eta_{U_k}}2\|d_k\|^2$
-- statement:
--   Let $F=f+\psi$ with $f$ differentiable and $L_U$ smooth along a matrix $U\in\mathcal U$ (display (2)). Let $\eta>0$, let $H=H_{f,U}$ be the step parameter of Algorithm 1 (in either of its two cases), and let $d$ be a global minimizer over $\mathbb R^p$ of the subproblem (9) at a point $x\in\mathbb R^n$. Then
--
--   $$
--   F(x+Ud)\le F(x)-\frac{\eta}{2}\|d\|^2 .
--   $$
--
--   Applied at every iteration of SCPG ($x=x_k$, $U=U_k$, $\eta=\eta_{U_k}$, $d=d_k$), this is the descent inequality $F(x_{k+1})\le F(x_k)-\frac{\eta_{U_k}}{2}\|d_k\|^2$ for all $k\ge0$. It makes $F$ a Lyapunov function for SCPG and keeps all iterates in $\mathcal L_F(x_0)$.
--
--   Differences from the source:
--   - generalization: the iterates of SCPG, for all k ≥ 0 → any point x, any U ∈ 𝒰, any η > 0 and any global minimizer d of (9) at (x, U, H_{f,U}); reason: every iteration of every run is an instance
--   - generalization: Assumption 1 (A.1 for 𝒰, ψ C² and simple, A.3) → f differentiable with (2) for this U; no regularity of ψ; no solution of (1); reason: the proof uses only (3) for U, the optimality of d, and convexity along subspaces in the first case; Assumption 1 implies these
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
--   - generalization: the set 𝒰 bounded (standing assumption, p.4); 𝓛_F(x₀) bounded (standing assumption, p.7: "Throughout the paper, we also assume boundedness of the level set") → not assumed; reason: the proof does not use them; they serve only to make H_{F,max} finite, which this statement does not involve; every instance satisfying them is covered
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 4, display (16), p.9

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_Hf
import Definitions.Def_StochCoordProx_model

open Matrix

namespace StochCoordProx

/-- **Lemma 4 (descent inequality).** One step of SCPG decreases `F = f + ψ`: if `U ∈ 𝒰`, `f` is
differentiable and `L_U` smooth along `U`, `η > 0`, `H = H_{f,U}` is the step parameter of
Algorithm 1 (both cases of the rule), and `d` is a global minimizer of the subproblem (9) at `x`,
then for `x⁺ = x + U d`
`F(x⁺) ≤ F(x) − (η/2) ‖d‖²`  (16).

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 4, display (16), p.9.

**Formalization Note.** Stated for one step at an arbitrary point `x`; every iteration `k` of
every SCPG run is an instance (`x = x_k`, `U = U_k`, `η = η_{U_k}`, `d = d_k`). No regularity of
`ψ` and no solution of (1) is assumed. -/
theorem lemma_4_descent {n p : ℕ} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (U : Matrix (Fin n) (Fin p) ℝ) (hU : U ∈ 𝒰)
    (LU η : ℝ) (hf : Differentiable ℝ f) (hL : IsSmoothAlong f U LU) (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin p))
    (hd : ∀ d' : EuclideanSpace ℝ (Fin p),
      model f ψ x U (Hf ψ 𝒰 LU η) d ≤ model f ψ x U (Hf ψ 𝒰 LU η) d') :
    f (x + Matrix.toEuclideanLin U d) + ψ (x + Matrix.toEuclideanLin U d) ≤
      f x + ψ x - η / 2 * ‖d‖ ^ 2 := by sorry

end StochCoordProx

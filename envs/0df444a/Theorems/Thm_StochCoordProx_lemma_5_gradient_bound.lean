-- Prove2me | Theorems.Thm_StochCoordProx_lemma_5_gradient_bound
-- name    : StochCoordProx.lemma_5_gradient_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:10.33154+00:00
-- url     : https://prove2.me/theorems/7289bb60-bfbf-4e5b-8fa7-27d64086dc61
-- title:
--   Lemma 5 — $\|\nabla F(x_k)\|^2\le\frac{H_{F,U_k}^2}{\alpha^2}\|d_k\|^2$ on well-aligned iterations
-- statement:
--   Let $F=f+\psi$ with $f$ differentiable and $L_U$ smooth along $U\in\mathcal U$, and $\psi$ twice continuously differentiable. Let $\eta>0$, $H=H_{f,U}$, and let $d$ be a global minimizer of the subproblem (9) at a point $x\in\mathcal L_F(x_0)=\{y:F(y)\le F(x_0)\}$. Let $\alpha\in(0,1)$ and suppose $U$ is well-aligned at $x$: $\|U^T\nabla F(x)\|\ge\alpha\|\nabla F(x)\|$. If $B$ bounds $H_{F,U}$, i.e. $\|U^T\bar\nabla^2\Psi(z_1,\dots,z_n)U+H I_{p\times p}\|_F\le B$ for all $z_1,\dots,z_n\in\operatorname{conv}(\mathcal L_F(x_0))$, then
--
--   $$
--   \|\nabla F(x)\|^2\le\frac{B^2}{\alpha^2}\|d\|^2 .
--   $$
--
--   With $B=H_{F,U_k}$ and $x=x_k$ for $k\in\mathbb A_K$ this is display (19), $\|\nabla F(x_k)\|^2\le\frac{H_{F,U_k}^2}{\alpha^2}\|d_k\|^2$. It converts the decrease of Lemma 4 into a bound on the gradient on well-aligned steps.
--
--   Differences from the source:
--   - generalization: the iterates of SCPG, k ∈ 𝔸_K → any x ∈ 𝓛_F(x₀), any U ∈ 𝒰 well-aligned at x, any η > 0 and any global minimizer d of (9); reason: every well-aligned iteration of a run is an instance, since x_k ∈ 𝓛_F(x₀) by Lemma 4
--   - generalization: Assumption 2 → only the alignment of this step; reason: the proof uses only that U_k is well-aligned
--   - generalization: 𝓛_f(x₀) bounded, and the constant H_{F,U_k} of (18) → any B with IsCurvBound (‖U^T∇̄²Ψ(z)U + H I‖_F ≤ B on conv 𝓛_F(x₀)); reason: boundedness is used only to make H_{F,U} finite; B = H_{F,U} is an instance, the max being attained on the compact set
--   - generalization: A.3 and A.1 for every matrix of 𝒰 → not assumed; (2) only for this U; reason: not used by the proof
--   - reading: 𝓛_f(x₀) → 𝓛_F(x₀) = {y : F(y) ≤ F(x₀)}; reason: the only sublevel set the paper defines (p.7); (18) and the proof of Lemma 5 use conv(𝓛_F(x₀)); boundedness of {f ≤ f(x₀)} would not make H_{F,U} finite
--   - encoding: ψ is simple (A.2) → not stated; reason: a computational remark (the prox of ψ along U is cheap), not a mathematical condition
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
--   - generalization: the set 𝒰 bounded (standing assumption, p.4) → not assumed; reason: the proof uses only the bound B of the curvature matrix, which is a hypothesis; every bounded 𝒰 is an instance
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 5, display (19), p.10

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_Hf
import Definitions.Def_StochCoordProx_model
import Definitions.Def_StochCoordProx_WellAligned
import Definitions.Def_StochCoordProx_IsCurvBound

open Matrix

namespace StochCoordProx

/-- **Lemma 5 (gradient bounded by the step on well-aligned iterations).** Let `f` be
differentiable and `L_U` smooth along `U ∈ 𝒰`, let `ψ` be twice continuously differentiable, let
`η > 0`, `H = H_{f,U}` (Algorithm 1, step 1), and let `d` be a global minimizer of the subproblem
(9) at a point `x` of the sublevel set `𝓛_F(x₀)`, `F = f + ψ`. Let `α ∈ (0,1)` and suppose `U` is
well-aligned at `x`: `‖Uᵀ∇F(x)‖ ≥ α‖∇F(x)‖`. If `B` bounds `H_{F,U}` (display (18)), then
`‖∇F(x)‖² ≤ (B²/α²) ‖d‖²`; with `B = H_{F,U}` this is (19).

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 5, display (19), p.10.

**Formalization Note.** Stated for one step at an arbitrary `x ∈ 𝓛_F(x₀)`; every well-aligned
iteration `k ∈ 𝔸_K` of a run is an instance. Only the alignment of this step is assumed (not
Assumption 2), and boundedness of `𝓛_F(x₀)` is replaced by the bound `B` it is used to provide.
`H_{F,U}` is the least `B` with `IsCurvBound`. The paper's "𝓛_f(x₀)" is read as `𝓛_F(x₀)`. -/
theorem lemma_5_gradient_bound {n p : ℕ} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (U : Matrix (Fin n) (Fin p) ℝ) (hU : U ∈ 𝒰)
    (LU η : ℝ) (hf : Differentiable ℝ f) (hL : IsSmoothAlong f U LU) (hψ : ContDiff ℝ 2 ψ)
    (hη : 0 < η) (x₀ x : EuclideanSpace ℝ (Fin n)) (hx : f x + ψ x ≤ f x₀ + ψ x₀)
    (d : EuclideanSpace ℝ (Fin p))
    (hd : ∀ d' : EuclideanSpace ℝ (Fin p),
      model f ψ x U (Hf ψ 𝒰 LU η) d ≤ model f ψ x U (Hf ψ 𝒰 LU η) d')
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (halign : WellAligned α (gradient (fun y => f y + ψ y) x) U)
    (B : ℝ) (hB : IsCurvBound f ψ x₀ U (Hf ψ 𝒰 LU η) B) :
    ‖gradient (fun y => f y + ψ y) x‖ ^ 2 ≤ B ^ 2 / α ^ 2 * ‖d‖ ^ 2 := by sorry

end StochCoordProx

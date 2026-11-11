-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_conditional_resampling_properties
-- name    : QuantumTriangleFinding.Search.conditional_resampling_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:46.525078+00:00
-- url     : https://prove2.me/theorems/fd0b4f6a-85ee-44b1-a2fb-7883068fff9d
-- title:
--   Lemma 4.2 — Properties of conditional resampling
-- statement:
--   Let $\rho$ be any finite Boolean input law, $w_i\ge0$, $R>0$, $H=\sum_iw_iD_{\rho,i}$ and $F=(I+H/R)^{-1}$. Then $F$ is self-adjoint and
--   $$0\preceq F^2\preceq F\preceq I,\qquad F|\rho\rangle=|\rho\rangle,\qquad \|Ff\|_\infty\le\|f\|_\infty.$$
--   For every input-register operator $H'\succeq H$, writing $F'=(I+H'/R)^{-1}$ gives
--   $$0\preceq(F')^2\preceq F'\preceq F.$$
--   For every input-register operator $B$, with no self-adjointness requirement on $B$,
--   $$[B,F]=R^{-1}F[H,B]F,\qquad \langle Ff,HFf\rangle\le\frac R4\|f\|^2.$$
--   All vector statements hold in every finite complex workspace, and both infinity norms use $\rho$. This states every clause for arbitrary dependent input laws and arbitrary nonnegative resampling weights, including all-zero weights.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 4.2, (4.7)–(4.10), p. 18

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 4.2, p.18, including order reversal, unrestricted B and the exact R/4 energy bound. -/
theorem conditional_resampling_properties {I W : Type} [Fintype I] [Fintype W]
    (ρ : (I → Bool) → ℝ) (hρ : IsProbability ρ) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (R : ℝ) (hR : 0 < R) :
    let H := weightedDifferences ρ w
    let F := resolvent H R
    SelfAdjoint ρ F ∧
    OperatorLE ρ 0 (F * F) ∧ OperatorLE ρ (F * F) F ∧ OperatorLE ρ F 1 ∧
    F.mulVec (fun _ => 1) = (fun _ => 1) ∧
    (∀ f : Joint ρ W, infinityNorm ρ (applyKernel F f) ≤ infinityNorm ρ f) ∧
    (∀ H' : Matrix (Support ρ) (Support ρ) ℂ, OperatorLE ρ H H' →
      let F' := resolvent H' R
      OperatorLE ρ 0 (F' * F') ∧ OperatorLE ρ (F' * F') F' ∧ OperatorLE ρ F' F) ∧
    (∀ B : Matrix (Support ρ) (Support ρ) ℂ,
      commutator B F = (R : ℂ)⁻¹ • (F * commutator H B * F)) ∧
    (∀ f : Joint ρ W,
      (jointInner ρ (applyKernel F f) (applyKernel H (applyKernel F f))).re ≤
        (R / 4) * normSq ρ f) := by sorry

end QuantumTriangleFinding.Search

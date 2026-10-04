-- Prove2me | Theorems.Thm_PolyakovAction_diffeomorphism_invariance
-- name    : PolyakovAction.diffeomorphism_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T10:05:27.278201+00:00
-- url     : https://prove2.me/theorems/50a0258b-86c8-4a5a-a7fd-2d88a7d08a61
-- title:
--   Invariance under worldsheet diffeomorphisms
-- statement:
--   Let $\varphi$ be a change of worldsheet coordinates $\sigma=\varphi(\tilde\sigma)$ that is injective and differentiable on an open set $s$, with Jacobian matrix $J=\partial\sigma/\partial\tilde\sigma$. Transform the worldsheet metric as a tensor, $\tilde h_{ab}(\tilde\sigma)=\frac{\partial\sigma^c}{\partial\tilde\sigma^a}\frac{\partial\sigma^d}{\partial\tilde\sigma^b}h_{cd}(\varphi(\tilde\sigma))$, and the embedding as a scalar, $\tilde X=X\circ\varphi$. If $X$ is differentiable on $\varphi(s)$, then
--   $$S[\tilde h,\tilde X;\,s]=S[h,X;\,\varphi(s)].$$
--
--   This is the source's local symmetry under worldsheet diffeomorphisms: $h^{ab}$ transforms with the Jacobian, $\tilde h=J^2h$, and $\sqrt{-\tilde h}\,d^2\tilde\sigma$ compensates the change of measure.
--
--   **Formalization Note.** The transformed metric is written as $J^{\mathsf T}h(\varphi(\tilde\sigma))J$ with $J$ the matrix of the derivative $\varphi'(\tilde\sigma)$; this is equivalent to the source's transformation of the inverse metric $h^{ab}$. No invertibility of $J$ is assumed.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem diffeomorphism_invariance {D : ℕ} (T : ℝ)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (φ : Worldsheet → Worldsheet) (φ' : Worldsheet → (Worldsheet →L[ℝ] Worldsheet))
    (s : Set Worldsheet) (hs : IsOpen s) (hφ : ∀ x ∈ s, HasFDerivAt φ (φ' x) x)
    (hinj : Set.InjOn φ s) (hX : ∀ x ∈ s, DifferentiableAt ℝ X (φ x)) :
    polyakovAction T g
        (fun σ' => (LinearMap.toMatrix' (φ' σ').toLinearMap)ᵀ * h (φ σ')
          * LinearMap.toMatrix' (φ' σ').toLinearMap)
        (X ∘ φ) s
      = polyakovAction T g h X (φ '' s) := by sorry

end PolyakovAction

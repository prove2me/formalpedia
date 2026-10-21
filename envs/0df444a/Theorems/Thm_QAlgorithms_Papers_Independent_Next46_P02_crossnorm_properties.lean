-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_crossnorm_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P02.crossnorm_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:23:08.19587+00:00
-- url     : https://prove2.me/theorems/1e99c624-c1bd-4cd7-95b0-8813e12b16f8
-- title:
--   The five reasonable-crossnorm properties
-- statement:
--   Let $X,Y$ be real or complex Banach spaces and let $X^*,Y^*$ denote their continuous duals. Write $\varepsilon$ and $\pi$ for the injective and projective functions on the algebraic tensor product. Their definitions are
--
--   $$
--   \varepsilon(u)=\sup_{\|f\|,\|g\|\le1}|(f\otimes g)(u)|,\qquad
--   \pi(u)=\inf_{u=\sum_{k=1}^n x_k\otimes y_k}\sum_{k=1}^n\|x_k\|\|y_k\|.
--   $$
--
--   A norm $\alpha$ is reasonable when $\alpha(x\otimes y)\le\|x\|\|y\|$ and every $f\otimes g$ is continuous with dual norm at most $\|f\|\|g\|$. All five assertions hold: (i) $\alpha(x\otimes y)=\|x\|\|y\|$; (ii) the $\alpha$-dual norm restricted to the algebraic tensor product $X^*\otimes Y^*$ is a reasonable crossnorm on that tensor product, relative to its continuous dual; (iii) $\varepsilon$ and $\pi$ are norms; (iv) both are reasonable; and (v), for every norm $\alpha$,
--
--   $$
--   \alpha\text{ is reasonable}\iff \varepsilon(u)\le\alpha(u)\le\pi(u)\text{ for every }u\in X\otimes Y.
--   $$
--
--   These assertions distinguish algebraic dual tensors from completed projective tensors.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 3, §3, unnumbered crossnorm assertions (i)–(v)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Banach

variable {X Y V W : Type*}

variable [NormedAddCommGroup X] [NormedSpace F X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace F Y] [CompleteSpace Y]

variable [NormedAddCommGroup V] [NormedSpace F V] [CompleteSpace V]

variable [NormedAddCommGroup W] [NormedSpace F W] [CompleteSpace W]

/-- PDF p.3, assertions (i)–(v): simple-tensor equality; algebraic dual
restriction; both norm axioms; reasonableness; and the extremal characterization. -/
theorem crossnorm_properties [CompleteSpace X] [CompleteSpace Y] :
    (∀ a : TensorProduct F X Y → ℝ, ReasonableCrossnorm a →
      ∀ (x : X) (y : Y), a (x ⊗ₜ[F] y) = ‖x‖ * ‖y‖) ∧
    (∀ a : TensorProduct F X Y → ℝ, ReasonableCrossnorm a →
      ReasonableCrossnorm (restrictedDualNorm a)) ∧
    (NormOn (F := F) (fun _ : TensorProduct F X Y => True) injectiveNorm ∧
      NormOn (F := F) (fun _ : TensorProduct F X Y => True) algebraicProjectiveNorm) ∧
    (ReasonableCrossnorm (F := F) (X := X) (Y := Y) injectiveNorm ∧
      ReasonableCrossnorm (F := F) (X := X) (Y := Y) algebraicProjectiveNorm) ∧
    (∀ a : TensorProduct F X Y → ℝ, NormOn (F := F) (fun _ => True) a →
      (ReasonableCrossnorm a ↔ ∀ u, injectiveNorm u ≤ a u ∧ a u ≤ algebraicProjectiveNorm u)) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Next46.P02

end

-- Prove2me | Theorems.Thm_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul
-- name    : TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/39f89b60-b8f7-5398-9fa1-4d9f1f97c3e3
-- title:
--   Transporting a tensor product along a field isomorphism
-- statement:
--   Let $e \colon k \xrightarrow{\sim} \kappa$ be a ring isomorphism of fields, let $V$ be a $k$-vector space and $H$ a $\kappa$-vector space (all carried by types in `Type`). Equip $V$ with the $\kappa$-action obtained by restricting scalars along $e^{-1}$, and $H$ as well as $V \otimes_\kappa H$ with the $k$-actions obtained by restricting scalars along $e$, in each case via `Module.compHom`. The assertion is threefold. First, $H$ is a finite module over $k$ if and only if it is finite over $\kappa$. Second, $\operatorname{finrank}_k H = \operatorname{finrank}_\kappa H$ (with the usual Mathlib convention that the rank is $0$ when the module is not finite). Third, there exists a $k$-linear isomorphism $\Theta \colon V \otimes_k H \xrightarrow{\sim} V \otimes_\kappa H$ such that $\Theta(v \otimes_k h) = v \otimes_\kappa h$ for all $v \in V$, $h \in H$, and such that $\Theta$ intertwines the two versions of `TensorProduct.map`: for every $k$-linear $f \colon V \to V$ and $\kappa$-linear $f' \colon V \to V$ agreeing pointwise, and every $\kappa$-linear $g \colon H \to H$ and $k$-linear $g' \colon H \to H$ agreeing pointwise, one has $\Theta \circ (f \otimes g') = (f' \otimes g) \circ \Theta$ on all of $V \otimes_k H$.
--
--   This is base-change bookkeeping: in Mathlib the ground ring is a parameter of `TensorProduct`, so $V \otimes_k H$ and $V \otimes_\kappa H$ are distinct types even after the scalar actions have been identified along $e$, and the statement provides the comparison isomorphism together with the invariance of finiteness and of rank under restriction of scalars along a ring isomorphism. It is used in the deformation-theoretic computation [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP), where tangent spaces over a field are compared with tangent spaces over an isomorphic copy of that field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul
    {k κ : Type} [Field k] [Field κ] (e : k ≃+* κ)
    (V : Type) [AddCommGroup V] [Module k V] (H : Type) [AddCommGroup H] [Module κ H] :
    letI : Module κ V := Module.compHom V (e.symm : κ ≃+* k).toRingHom
    letI : Module k H := Module.compHom H e.toRingHom
    letI : Module k (V ⊗[κ] H) := Module.compHom (V ⊗[κ] H) e.toRingHom
    (Module.Finite k H ↔ Module.Finite κ H) ∧
    Module.finrank k H = Module.finrank κ H ∧
    ∃ Θ : (V ⊗[k] H) ≃ₗ[k] (V ⊗[κ] H),
      (∀ (v : V) (h : H), Θ (v ⊗ₜ[k] h) = v ⊗ₜ[κ] h) ∧
      (∀ (f : V →ₗ[k] V) (f' : V →ₗ[κ] V) (_ : ∀ v, f' v = f v) (g : H →ₗ[κ] H) (g' : H →ₗ[k] H) (_ : ∀ h, g' h = g h)
          (x : V ⊗[k] H),
        Θ (TensorProduct.map f g' x) = TensorProduct.map f' g (Θ x)) := by sorry

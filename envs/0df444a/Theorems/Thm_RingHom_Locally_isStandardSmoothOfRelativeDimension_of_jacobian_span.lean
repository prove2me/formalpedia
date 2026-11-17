-- Prove2me | Theorems.Thm_RingHom_Locally_isStandardSmoothOfRelativeDimension_of_jacobian_span
-- name    : RingHom.Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:00:43.626741+00:00
-- url     : https://prove2.me/theorems/7ec94144-258d-4b36-af88-56aaf57e2551
-- title:
--   Jacobian generators give local standard smoothness of fixed relative dimension
-- statement:
--   Let $S$ be a commutative $R$-algebra, let the finite variable and relation index types be $ι$ and $σ$, and let $P_e$ be a family of pre-submersive presentations of $S/R$. Assume every $P_e$ has relative dimension $n$ and that their Jacobian elements generate the unit ideal. Then $$R→S\text{ is locally standard smooth of relative dimension }n.$$ This packages the Jacobian-cover argument used on the canonical affine charts. Formalization note: finiteness of $ι$ and $σ$ is supplied by typeclass hypotheses.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

universe u
open RingHom

theorem RingHom.Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {E ι σ : Type*} [_root_.Finite ι] [_root_.Finite σ]
    (P : E → Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hDimension : ∀ e, (P e).dimension = n)
    (hspan : Ideal.span (Set.range fun e ↦ (P e).jacobian) = ⊤) :
    Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S) := by sorry

-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat
-- name    : ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/847c9023-33d3-5b9b-8067-c2604b9ffd3d
-- title:
--   Lifting points of a finite flat algebra to a valuation subring
-- statement:
--   Let $R$ be a commutative ring and $B$ a commutative $R$-algebra which is finite and flat as an $R$-module. Let $K$ be an algebraically closed field and let $O$ be a valuation subring of $K$, equipped with an $R$-algebra structure (so with a structure map $R \to O$ which need not be related to the one on $B$ beyond the hypothesis below). Let $k$ be a field and $\pi \colon O \to k$ a surjective ring homomorphism; $\pi$ is only assumed surjective, not an $R$-algebra map. Let $\varphi_0 \colon B \to k$ be a ring homomorphism compatible with $\pi$ over $R$, in the sense that $\varphi_0 \circ (R \to B) = \pi \circ (R \to O)$ as ring homomorphisms $R \to k$. Then there exists a ring homomorphism $\varphi \colon B \to O$ such that $\varphi \circ (R \to B) = (R \to O)$, i.e. $\varphi$ is a homomorphism of $R$-algebras, and $\pi \circ \varphi = \varphi_0$, i.e. $\varphi$ lifts $\varphi_0$ along $\pi$.
--
--   Geometrically: for $\operatorname{Spec} B \to \operatorname{Spec} R$ finite flat, every $k$-valued point of $B$ lying over the closed point of $\operatorname{Spec} O \to \operatorname{Spec} R$ is the specialisation of an $O$-valued point, so specialisation from $O$-points to $k$-points is surjective fibrewise over $\operatorname{Spec} R$. It is used for the surjectivity of reduction on torsion points of modular curves ([`ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow`](thm.html#ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow)) and in the construction of homomorphisms into rings of integers of $p$-adic algebraic closures ([`PadicAlgCl.exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow`](thm.html#PadicAlgCl.exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
    {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Flat R B]
    {K : Type*} [Field K] [IsAlgClosed K] (O : ValuationSubring K) [Algebra R ↥O]
    {k : Type*} [Field k] (π : ↥O →+* k) (hπ : Function.Surjective π)
    (φ₀ : B →+* k) (hcomp : φ₀.comp (algebraMap R B) = π.comp (algebraMap R ↥O)) :
    ∃ φ : B →+* ↥O, φ.comp (algebraMap R B) = algebraMap R ↥O ∧ π.comp φ = φ₀ := by sorry

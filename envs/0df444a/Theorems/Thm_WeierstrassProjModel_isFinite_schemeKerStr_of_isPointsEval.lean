-- Prove2me | Theorems.Thm_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval
-- name    : WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/78ae088e-7cc9-527c-8a16-81d98bdfef17
-- title:
--   Finiteness of n-torsion kernel schemes of a relative group law
-- statement:
--   Let $R$ be a commutative ring and $V$ a projective Weierstrass curve over $R$, with `projModelCR V` the $\mathrm{Proj}$ of the graded quotient attached to $V$ and `projModelStrCR V` its structure morphism to $\mathrm{Spec}\,R$. Assume: (i) for every field $K$ with an $R$-algebra structure, the fibre product of `projModelStrCR V` with $\mathrm{Spec}\,K \to \mathrm{Spec}\,R$ is isomorphic to the projective model of the base change $V_K$; (ii) $G$ is a relative group law on `projModelStrCR V`, that is, a functorial group structure (multiplication, unit, inverse, associativity, unit and inverse laws, and naturality of multiplication under base change) on the sets $\{\varphi : T \to A \mid \varphi \text{ is over } \mathrm{Spec}\,R\}$; (iii) $ev$ is a family of bijections, for each field $F$ over $R$, from the $F$-points of the model over $\mathrm{Spec}\,R$ to the affine points of $V_F$, satisfying `IsPointsEval`, i.e. each $ev_F$ carries $G$-multiplication to addition of points and Galois twisting by $\sigma \in \mathrm{Aut}_R(F)$ to `Point.map` along $\sigma$; (iv) for every algebraically closed field $F$ over $R$ and every prime $\ell$ with $\ell \neq 0$ in $F$, some nonzero point of $V_F$ is killed by $\ell$. Then for every $n > 0$ the projection to $\mathrm{Spec}\,R$ of the pullback of multiplication by $n$ on the model along the unit section — the kernel scheme `G.schemeKerStr n` — is a finite morphism.
--
--   This is the finiteness of the $n$-torsion subscheme $A[n] \to \mathrm{Spec}\,R$ of the projective Weierstrass model equipped with its relative group law, the input needed to realise $A[n]$ as the spectrum of a finite Hopf algebra over $R$. It is used in the constructions of finite flat Hopf models of torsion at good primes and of the associated finite free Hopf algebras over $\mathbf{Z}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval
    {R : Type u} [CommRing R]
    (V : WeierstrassCurve.Projective R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0)
    {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeKerStr n) := by sorry

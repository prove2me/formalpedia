-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P67_universalForm_functor_and_decompositions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P67.universalForm_functor_and_decompositions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:24:12.629253+00:00
-- url     : https://prove2.me/theorems/98db1c2e-7151-4f2a-90bd-c998b60e8406
-- title:
--   Functoriality and decompositions of the universal coefficient space
-- statement:
--   For a finite-dimensional real Lie algebra $\mathfrak g$, write $V(\mathfrak g)$ for its universal coefficient space. Every Lie homomorphism $f$ induces the map determined by
--
--   $$V(f)\kappa_u(x,y)=\kappa_u(fx,fy),\quad V(\mathrm{id})=\mathrm{id},\quad V(gf)=V(g)V(f).$$
--
--   1. If $\mathfrak g=\mathfrak a\oplus\mathfrak b$ and $\mathfrak a$ is perfect, then $V(\mathfrak g)\cong V(\mathfrak a)\oplus V(\mathfrak b)$, with the corresponding component formula on $\kappa_u$.
--   2. If the quotient $q:\mathfrak g\to\mathfrak q$ has a Lie section $s$, then $\mathfrak g\cong\ker(q)\rtimes\mathfrak q$, under $x\mapsto(x-s(qx),qx)$. The action is induced by $\operatorname{ad}\circ s$. The map $V(s)$ is injective and $V(q)V(s)=\mathrm{id}$. For coordinates $(u,a),(v,b)$, the bracket is $([u,v]+[s(a),v]-[s(b),u],[a,b])$.
--   3. A reductive decomposition $\mathfrak g=\mathfrak z(\mathfrak g)\oplus\bigoplus_{j=1}^n\mathfrak s_j$ into the center and simple ideals induces $V(\mathfrak g)\cong V(\mathfrak z(\mathfrak g))\oplus\bigoplus_{j=1}^nV(\mathfrak s_j)$.
--   4. A Levi decomposition $\mathfrak k=\mathfrak r\rtimes\mathfrak s$ induces an injection $V(\mathfrak s)\to V(\mathfrak k)$.
--
--   These statements explain how the universal coefficient space respects the given algebraic decompositions. Lean specifies each reductive decomposition by its actual summands, inclusions and Lie isomorphism; a Levi complement is a semisimple complement to the solvable radical.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, PDF p. 41, Remark B.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section Functor

variable {L : Type u} {M : Type v}

variable [LieRing L] [LieAlgebra ℝ L] [LieRing M] [LieAlgebra ℝ M]

/-- Remark B.2, PDF p. 41, all five parts. Perfectness in (b) is the span of
brackets being the whole algebra. In (c), a split quotient is supplied by its
actual quotient map and Lie section; the displayed bracket identifies the
result with the semidirect product by the section's adjoint action. In (d),
the chosen reductive center/simple-ideal decomposition is supplied as an
actual Lie isomorphism, and the conclusion specifies the corresponding map
on κu. In (e), a Levi complement means a semisimple complement of the solvable
radical, not an arbitrary subalgebra. -/
theorem universalForm_functor_and_decompositions
    (L : Type u) (M : Type v) (N : Type w)
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieRing M] [LieAlgebra ℝ M] [FiniteDimensional ℝ M]
    [LieRing N] [LieAlgebra ℝ N] [FiniteDimensional ℝ N] :
    (universalMap (LieHom.id : L →ₗ⁅ℝ⁆ L) = LinearMap.id) ∧
    (∀ (f : L →ₗ⁅ℝ⁆ M) (g : M →ₗ⁅ℝ⁆ N),
      universalMap (g.comp f) = (universalMap g).comp (universalMap f)) ∧
    (Submodule.span ℝ {z : L | ∃ x y : L, z = ⁅x, y⁆} = ⊤ →
      ∃ e : UniversalFormSpace (L × M) ≃ₗ[ℝ]
          UniversalFormSpace L × UniversalFormSpace M,
        ∀ (x y : L × M), e (universalForm (L × M) x y) =
          (universalForm L x.1 y.1, universalForm M x.2 y.2)) ∧
    (∀ (q : L →ₗ⁅ℝ⁆ M) (s : M →ₗ⁅ℝ⁆ L), q.comp s = LieHom.id →
      Function.Injective (universalMap s) ∧
      (universalMap q).comp (universalMap s) = LinearMap.id ∧
      ∃ e : L ≃ₗ[ℝ] (q.ker × M),
        (∀ x : L, (e x).2 = q x ∧ ((e x).1 : L) = x - s (q x)) ∧
        (∀ x y : L, ((e ⁅x, y⁆).1 : L) =
          ⁅((e x).1 : L), ((e y).1 : L)⁆ +
            ⁅s ((e x).2), ((e y).1 : L)⁆ -
            ⁅s ((e y).2), ((e x).1 : L)⁆)) ∧
    (∀ (n : ℕ) (J : Fin n → LieIdeal ℝ L),
      (∀ i, LieAlgebra.IsSimple ℝ (J i)) →
      ∀ e : L ≃ₗ⁅ℝ⁆ (LieAlgebra.center ℝ L × ((i : Fin n) → J i)),
      (∀ x : L, x = ((e x).1 : L) + ∑ i : Fin n, ((e x).2 i : L)) →
      ∃ eV : UniversalFormSpace L ≃ₗ[ℝ]
          (UniversalFormSpace (LieAlgebra.center ℝ L) ×
            ((i : Fin n) → UniversalFormSpace (J i))),
        ∀ x y : L, eV (universalForm L x y) =
          (universalForm (LieAlgebra.center ℝ L) (e x).1 (e y).1,
            fun i => universalForm (J i) ((e x).2 i) ((e y).2 i))) ∧
    (∀ s : LieSubalgebra ℝ L,
      LieAlgebra.IsSemisimple ℝ s →
      IsCompl (LieAlgebra.radical ℝ L).toSubmodule s.toSubmodule →
      Function.Injective (universalMap s.incl)) := by sorry

end Functor

end QAlgorithms.Papers.Independent.Intakenext100.P67

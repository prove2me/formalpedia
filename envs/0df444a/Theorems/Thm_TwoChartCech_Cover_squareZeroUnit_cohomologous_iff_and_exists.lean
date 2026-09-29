-- Prove2me | Theorems.Thm_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists
-- name    : TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/3e4dbd50-0dd8-5997-9b0f-ce910665addd
-- title:
--   Čech H¹ and principal units of a square-zero thickening
-- statement:
--   Let $K$ be a field and let $\mathcal{U}$ consist of commutative $K$-algebras $A_0$, $A_1$, $A_{01}$ together with $K$-algebra maps $\rho_0 \colon A_0 \to A_{01}$ and $\rho_1 \colon A_1 \to A_{01}$ (an abstract two-chart cover). Let $V$ be a $K$-module, with the bimodule data making the trivial square-zero extension $A = K \oplus V$ a $K$-algebra, and write $\pi \colon A \otimes_K A_{01} \to A_{01}$ for the algebra map induced by the first projection $A \to K$ and the identity on $A_{01}$, and $\sigma$ for the $K$-linear map $A \otimes_K A_{01} \to A_{01} \otimes_K V$ given by the second projection $A \to V$ followed by the commutativity isomorphism. For the structure sheaf of the cover — the sections datum with modules $A_0, A_1, A_{01}$ and restrictions $\rho_0, \rho_1$ — the Čech differential is $(m_0,m_1) \mapsto -\rho_0(m_0) + \rho_1(m_1)$, so its range is $\rho_0(A_0) + \rho_1(A_1)$ and $\check H^1$ is the quotient $A_{01}/(\rho_0(A_0)+\rho_1(A_1))$; let $q \colon A_{01} \otimes_K V \to \check H^1 \otimes_K V$ be the quotient map tensored with $V$. The assertion is the conjunction of two statements. First, for all units $t, t'$ of $A \otimes_K A_{01}$ with $\pi(t) = \pi(t') = 1$, there exist units $a_0$ of $A \otimes_K A_0$ and $a_1$ of $A \otimes_K A_1$ with $t' = (\mathrm{id} \otimes \rho_0)(a_0)\, t\, (\mathrm{id} \otimes \rho_1)(a_1^{-1})$ if and only if $q(\sigma(t)) = q(\sigma(t'))$. Second, every $y \in \check H^1 \otimes_K V$ equals $q(\sigma(t))$ for some unit $t$ of $A \otimes_K A_{01}$ with $\pi(t) = 1$.
--
--   This is the Čech cocycle computation underlying the identification of the kernel of $\operatorname{Pic}(X \times_K \operatorname{Spec}(K \oplus V)) \to \operatorname{Pic} X$ with $H^1(X, \mathcal{O}_X) \otimes_K V$, here in the two-chart setting: principal units $1 + w$ of the thickened overlap ring are classified, up to coboundaries from the two charts, by the class of their $V$-part, and every class arises. It is used in the construction of deformations of line bundles trivial modulo the square-zero ideal, via [`AlgebraicGeometry.RelPicard.exists_trivialModDeformations_map_H1_tensor_natural`](thm.html#AlgebraicGeometry.RelPicard.exists_trivialModDeformations_map_H1_tensor_natural).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists
    {K : Type u} [Field K] (𝒰 : TwoChartCech.Cover.{u, u} K)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    (∀ t t' : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      ((∃ (a0 : (TrivSqZeroExt K V ⊗[K] 𝒰.A0)ˣ) (a1 : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ),
          (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) =
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ0 (a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) *
              (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) *
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ1
              ((↑a1⁻¹ : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ) : TrivSqZeroExt K V ⊗[K] 𝒰.A1)) ↔
        (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) =
          (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01))))) ∧
    (∀ y : 𝒰.structureSheaf.H1 ⊗[K] V, ∃ t : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 ∧
      (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
          ((TensorProduct.comm K V 𝒰.A01).toLinearMap
            (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) = y) := by sorry

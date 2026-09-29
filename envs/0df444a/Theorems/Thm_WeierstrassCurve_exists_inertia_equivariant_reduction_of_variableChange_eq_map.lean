-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map
-- name    : WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/7bba088e-9568-55ee-85c2-5e7cc0d58a2e
-- title:
--   Inertia-equivariant good reduction of a Weierstrass model
-- statement:
--   Let $F$ and $M$ be fields with $M$ an $F$-algebra, let $A \subseteq M$ be a valuation subring, with residue field $\mathrm{ResidueField}(A)$ and residue map `residue A`, let $E$ be a Weierstrass curve over $F$, let $W$ be a Weierstrass curve with coefficients in $A$, and let $\kappa$ be a variable change over $M$ (decidable equality on $M$ and on the residue field is assumed). Suppose $\kappa$ carries the base change $E_M$ to the curve obtained from $W$ by the inclusion $A \hookrightarrow M$, i.e. $\kappa \bullet E_M = W_M$, and that the discriminant $\Delta(W)$ is a unit of $A$. Then there are an additive homomorphism $\theta$ from the group of affine points of $E_M$ to the group of affine points of the reduced curve $\widetilde W := W \bmod \mathfrak m_A$, and an assignment $g$ of a variable change $g_\sigma$ over $A$ to each $F$-automorphism $\sigma$ of $M$, such that: (i) for every natural number $n$ whose image in the residue field is nonzero and every affine point $P$ of $E_M$, $n \cdot P = 0$ and $\theta(P) = 0$ force $P = 0$; (ii) for every $\sigma$ in the decomposition subgroup of $A$ over $F$ whose associated element lies in the inertia subgroup, the image of $g_\sigma$ in variable changes over $M$ equals $\kappa \cdot (\sigma \kappa)^{-1}$ (where $\sigma$ acts on the coefficients of $\kappa$), the reduction of $g_\sigma$ fixes $\widetilde W$, i.e. $\bar g_\sigma \bullet \widetilde W = \widetilde W$, and for every affine point $P$ of $E_M$ the point obtained from $\theta(P)$ by the inverse coordinate change `Point.vcInvFun` for $\bar g_\sigma$ (which sends $0$ to $0$ and an affine point $(x,y)$ to $(u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$ for $\bar g_\sigma = (u,r,s,t)$) agrees, as a heterogeneous equality of points of the two curves identified by the preceding clause, with $\theta(\sigma P)$; and (iii) for all $\sigma,\tau$ in the decomposition subgroup whose associated elements lie in the inertia subgroup, $\bar g_{\sigma\tau} = \bar g_\sigma \bar g_\tau$.
--
--   This is the local mechanism behind the theorem of Deuring and Serre–Tate that at a place of good reduction the inertia group acts on torsion of order prime to the residue characteristic through automorphisms of the reduced curve: it combines the reduction homomorphism of an integral model with unit discriminant, its injectivity on prime-to-$p$ torsion, and the integrality of the coordinate change between two such models. It is used by [`ModularCurve.exists_equivariant_torsion_reduction_ofJ`](thm.html#ModularCurve.exists_equivariant_torsion_reduction_ofJ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u v in

theorem WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
    {F : Type u} {M : Type v} [Field F] [Field M] [DecidableEq M] [Algebra F M]
    (A : ValuationSubring M) [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) := by sorry

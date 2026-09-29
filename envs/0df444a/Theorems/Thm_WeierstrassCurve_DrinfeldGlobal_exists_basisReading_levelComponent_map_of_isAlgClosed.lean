-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_basisReading_levelComponent_map_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/701c3d8a-caff-5961-9f80-f543aef722c7
-- title:
--   Drinfeld level-q bases read as Galois-equivariant q-torsion bases
-- statement:
--   Fix $q\in\mathbb N$ with $q>0$ and a commutative ring $A$. Let $\mathcal G$ be a family of group laws over $A$, assigning to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta_W$ is a unit a relative group law on the $\mathrm{Proj}$ structure morphism $\mathtt{projModelStrCR}\,W$, and assume: $\mathcal G$ is chord–tangent, i.e. every member admits an evaluation $\mathrm{ev}$ with `IsPointsEval`; $\mathcal G$ has origin identity, i.e. for every member there is a ring homomorphism $\chi$ from the origin chart ring to $T$ which is an origin-chart section of the unit section and kills $\mathtt{xOverY}$ and $\mathtt{zOverY}$. Let $\mathcal T$ be a level transport datum for $(\mathcal G,q)$ — base-change maps and variable-change actions on raw Drinfeld pairs (a projective curve together with two sections), functorial and preserving the level-$q$ condition — satisfying the section-transport condition, which pins the transported sections by commuting squares with $\mathrm{Proj}$ of any graded homomorphism realising the variable change, resp. the coefficient homomorphism. Assume further that for every $A$-algebra homomorphism $f:T\to T'$ and every projective Weierstrass curve $W$ over $T$ such a graded homomorphism $\varphi$ of the projective-model graded quotient rings exists, with the irrelevant-ideal inequality and $\mathtt{IsCoefficientHom}$. Let $\Omega$ be an algebraically closed field of characteristic zero with decidable equality which is an $A$-algebra, $K_0$ a field that is an $A$-algebra with $\Omega$ a $K_0$-algebra compatibly ($A\to K_0\to\Omega$ a scalar tower), and $E$ an elliptic Weierstrass curve over $K_0$. Then there is a function $\Theta$ assigning to every raw Drinfeld pair $x$ over $\Omega$ an ordered pair of points of the affine curve of $E_\Omega=E.\mathrm{baseChange}\,\Omega$ such that, whenever $x$ is of level $q$ for $\mathcal G$ over $E_\Omega$ (that is, $x.\mathrm{curve}=E_\Omega$ and, for a unit discriminant, $(x.P,x.Q)$ is a Drinfeld basis of level $q$ for the corresponding member of $\mathcal G$): both components of $\Theta x$ are killed by $q$, every relation $a\cdot(\Theta x)_1+b\cdot(\Theta x)_2=0$ with $a,b\in\mathbb Z$ forces $q\mid a$ and $q\mid b$, and for every $K_0$-algebra automorphism $\sigma$ of $\Omega$ one has $\Theta(\mathcal T.\mathrm{map}\,\sigma\,x)=(\sigma_*(\Theta x)_1,\sigma_*(\Theta x)_2)$, where $\sigma$ is viewed as an $A$-algebra homomorphism and $\sigma_*$ is the induced map on points.
--
--   This is the comparison between Drinfeld $\Gamma(q)$-bases, in the sense of Katz–Mazur, on the projective model of an elliptic curve over an algebraically closed field of characteristic zero and ordinary bases of the group of $q$-torsion points, in a form that is equivariant for the automorphisms of $\Omega$ over the field of definition $K_0$. It is the Drinfeld input to the full-level moduli comparisons [`ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed`](thm.html#ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed) and [`ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

universe u

theorem WeierstrassCurve.DrinfeldGlobal.exists_basisReading_levelComponent_map_of_isAlgClosed
    (q : ℕ) (hq : 0 < q) (A : Type u) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra A Ω]
    (K₀ : Type u) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
    (E : WeierstrassCurve K₀) [E.IsElliptic] :
    ∃ Θ : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair Ω →
        (E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point,
      ∀ x : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair Ω,
        WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel 𝒢 q (E.baseChange Ω) x →
        (q • (Θ x).1 = 0 ∧ q • (Θ x).2 = 0 ∧
          ∀ a b : ℤ, a • (Θ x).1 + b • (Θ x).2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (𝒯.map ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) x) =
            (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ x).1,
              WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ x).2)) := by sorry

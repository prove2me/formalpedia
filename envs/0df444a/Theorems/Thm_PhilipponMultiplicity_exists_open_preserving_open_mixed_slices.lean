-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_open_mixed_slices
-- name    : PhilipponMultiplicity.exists_open_preserving_open_mixed_slices
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-08T03:57:40.297919+00:00
-- url     : https://prove2.me/theorems/b8b7cac6-fd71-4062-95a3-a25fe21f44c2
-- title:
--   Persistence of distinct mixed-section points from open quasi-finite charts
-- statement:
--   Let $W$ be a closed irreducible subvariety of a multiprojective space over a Philippon base field $K$. Choose mixed linear equations whose factor multiplicities sum to $\dim W$. Let $c_0$ be their initial coefficient array and let $S$ be a finite set of points in the corresponding intersection.
--
--   Assume that each $x\in S$ has a normalized projective representative, a principal affine chart with coordinate algebra $B$, and a $K$-algebra evaluation $e:B\to K$ that agrees with this representative on the original coordinates and with $c_0$ on the coefficient ring $C$. Suppose there is $f\in B$ such that
--   $$
--   e(f)\ne0,\qquad
--   \operatorname{Spec}B[1/f]\longrightarrow\operatorname{Spec}C
--   \text{ is open and quasi-finite}.
--   $$
--   Then there is a Zariski-open coefficient neighborhood $U$ containing the evaluation prime of $c_0$ such that every coefficient array $c$ whose evaluation prime belongs to $U$ admits an injection
--   $$
--   S\hookrightarrow W\cap\bigcap_j V(L_j(c)).
--   $$
--
--   This child is the remaining geometric persistence assertion after constructing open quasi-finite charts. It must preserve distinct points simultaneously and return actual projective $K$-points of the original equations. Openness of one chart only gives a prime over nearby parameters; it does not by itself construct the displayed injection. In particular, this statement does not assume that different selected points have disjoint Zariski-open neighborhoods in an irreducible space. No reducedness or transversality of the initial intersection is required.
-- source:
--   P. Philippon, « Lemmes de zéros dans les groupes algébriques commutatifs », Bulletin de la Société Mathématique de France 114 (1986), 355–383, mixed-linear-section interpretation after Lemma 3.1, p. 364; https://numdam.org/articles/10.24033/bsmf.2060/. This is an auxiliary persistence formulation for that argument, not a literal theorem in the source. Stacks Project, Lemma 37.41.5, Tag 02LO, https://stacks.math.columbia.edu/tag/02LO, gives an étale-local separation into finite pieces for a finite list of distinct isolated fiber points of a separated locally finite type morphism. That lemma is a possible ingredient; it does not alone prove this child's neighborhood, point descent, and simultaneous-injectivity conclusions.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_open_mixed_slices
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ f : MixedFamily.CoordinateRing M W l b H,
                e f ≠ 0 ∧
                IsOpenMap (PrimeSpectrum.comap (algebraMap (MixedFamily.ParameterRing M l)
                  (Localization.Away f))) ∧
                Algebra.QuasiFinite (MixedFamily.ParameterRing M l) (Localization.Away f)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by sorry

end PhilipponMultiplicity

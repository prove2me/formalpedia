-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_model_mixed_slices
-- name    : PhilipponMultiplicity.exists_open_preserving_finite_model_mixed_slices
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-07T16:49:26.044868+00:00
-- url     : https://prove2.me/theorems/5c4ce097-36ba-439a-866d-bebb597278df
-- title:
--   Persistence of mixed sections from finite algebra models
-- statement:
--   Let $W$ be a closed irreducible subvariety of a multiprojective space over a Philippon base field. Choose mixed linear equations with factor multiplicities summing to $\dim W$, an initial coefficient array $c_0$, and a finite set $S$ in the initial mixed intersection. Suppose each selected point admits normalized coordinates, a principal affine chart, and a compatible rational evaluation of its universal mixed incidence algebra $B$ over the coefficient ring $C$. Assume there is a finite $C$-subalgebra $D\subseteq B$ and $r\in D$ with
--   $$
--   e(r)\ne0,\qquad D[1/r]\xrightarrow{\sim}B[1/r]
--   $$
--   under the canonical localization map.
--
--   Then a Zariski-open coefficient neighborhood of $c_0$ admits an injection of $S$ into every mixed intersection whose coefficient evaluation prime belongs to that neighborhood. The finite model is localized only after asserting its finiteness; no finiteness of $D[1/r]$ over $C$ is assumed.
--
--   The checked reduction proves openness and quasi-finiteness of the localized model once the incidence algebra is a domain and the coefficient map is injective. It uses going-down over the normal polynomial coefficient ring, finite presentation, and the canonical localization isomorphism. Its two remaining open inputs are [domain and dominance of the incidence chart](p2m:theorem/7d5792da-5477-424b-9e70-e7125cacc289) and [persistence of distinct points from open quasi-finite charts](p2m:theorem/b8b7cac6-fd71-4062-95a3-a25fe21f44c2). These geometric statements are not consequences of finiteness alone. This is an auxiliary formulation of the mixed-section argument following Philippon's Lemma 3.1, pp. 363–364.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section discussion, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . The child is an auxiliary universal-family persistence synthesis, not a verbatim theorem of the paper. The finite local model used by the parent is supplied by algebraic Zariski's main theorem: Stacks Project, Theorem 10.123.12 (Tag 00Q9), https://stacks.math.columbia.edu/tag/00Q9 , including the finite-subalgebra construction in its proof. The exact formal input is Mathlib Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective, Mathlib/RingTheory/ZariskisMainTheorem.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO , suggests the etale separation step relevant to distinct-point persistence. The remaining dimension/dominance and persistence claims are explicit Open obligations, not direct consequences of quasi-finiteness for an arbitrary family.

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

theorem exists_open_preserving_finite_model_mixed_slices
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
              ∃ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
                Module.Finite (MixedFamily.ParameterRing M l) D ∧ ∃ r : D,
                  e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r)) →
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

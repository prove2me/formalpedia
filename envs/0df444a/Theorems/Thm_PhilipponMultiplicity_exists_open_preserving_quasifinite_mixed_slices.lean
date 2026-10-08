-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_quasifinite_mixed_slices
-- name    : PhilipponMultiplicity.exists_open_preserving_quasifinite_mixed_slices
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T16:28:29.047154+00:00
-- url     : https://prove2.me/theorems/21d579ca-f415-4857-ab2e-230dd9e2c4a2
-- title:
--   Persistence of quasi-finite universal mixed sections
-- statement:
--   Let $K$ be a Philippon base field and let $W$ be a closed irreducible subset of $M=\prod_i\mathbf P^{n_i}$. Choose $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the multigraded quotient Hilbert polynomial. Let $l=(i_0,\ldots,i_{s-1})$ list block $i$ exactly $\alpha_i$ times. Write $A=K[X_{i,t}]$, and for a coefficient array $c$ set
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   Z(c)=\{x\in W:P_j(c)(x)=0\text{ for every }j\}.
--   $$
--   Choose initial coefficients $c^0$ and a finite subset $S\subseteq Z(c^0)$.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries. For pivot indices $b_i$ and $H\in A$, define the universal affine mixed-slice algebra
--   $$
--   B_{b,H}=A[z][T_{j,w}]\Big/\Big(I(W),\ \big(\sum_t T_{j,(i_j,t)}X_{i_j,t}\big)_j,\ (X_{i,b_i}-1)_i,\ Hz-1\Big).
--   $$
--   This is a $C$-algebra by coefficient variables; equations from $A[z]$ are extended through constant polynomials. No radical is taken. Let $\mathfrak n_c\subset C$ be the evaluation maximal ideal at $c$.
--
--   Assume that for each $x\in S$ one can choose $b$, a normalized representative $v$ of $x$ with $v_{i,b_i}=1$, a polynomial $H$, and $a\in K$ such that $H(v)a=1$ and
--   $$
--   C\longrightarrow B_{b,H}\text{ is quasi-finite at every prime }\mathfrak q\subset B_{b,H}
--   \text{ satisfying }\mathfrak q\cap C=\mathfrak n_{c^0}.
--   $$
--   The entire initial fiber of each chosen affine chart is covered by this hypothesis; the chart and $H$ may depend on $x$. Quasi-finiteness is the standard local algebra property `Algebra.QuasiFiniteAt` of the indicated coefficient algebra map.
--
--   Then there is a Zariski-open subset $U\subseteq\operatorname{Spec}C$ with
--   $$
--   \mathfrak n_{c^0}\in U,\qquad
--   \mathfrak n_c\in U\ \Longrightarrow\ \text{there is an injection }S\hookrightarrow Z(c).
--   $$
--   The injection is chosen independently for each coefficient array. Empty $S$, empty equation lists, nonreduced fibers, and other components outside the chosen affine charts are allowed.
--
--   **Formalization Note.** A checked reduction constructs the evaluation homomorphism of each selected normalized projective point, proves that its kernel lies over the initial coefficient maximal ideal, and applies algebraic Zariski's main theorem to obtain a finite coefficient subalgebra whose localization agrees with a neighborhood of the point. The remaining [finite-model mixed-section persistence theorem](https://prove2.me/theorems/5c4ce097-36ba-439a-866d-bebb597278df) isolates dimension/dominance and persistence of distinct points on an open coefficient neighborhood. The original universal equations and possible nilpotents are retained. A localization of the finite subalgebra is not asserted finite over the whole coefficient ring.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section discussion, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . This auxiliary universal-family persistence statement is a synthesis, not a verbatim source theorem. Stacks Project, Lemma 29.21.7 (Tag 02NG), https://stacks.math.columbia.edu/tag/02NG , provides the finite-fiber/quasi-finiteness principle used in the parent reduction. The formal parent uses Mathlib Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt from Mathlib/RingTheory/ZariskisMainTheorem.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474; its algebraic Zariski-main-theorem input is Stacks Project, Theorem 10.123.12 (Tag 00Q9), https://stacks.math.columbia.edu/tag/00Q9 . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO , supplies an isolated-fiber etale-neighborhood strategy relevant to the remaining geometry. Neither source is claimed to directly prove the full specialized persistence statement.

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

theorem exists_open_preserving_quasifinite_mixed_slices
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
            ∀ q : PrimeSpectrum (MixedFamily.CoordinateRing M W l b H),
              q.asIdeal.under (MixedFamily.ParameterRing M l) =
                MvPolynomial.vanishingIdeal K {Function.uncurry c₀} →
              Algebra.QuasiFiniteAt (MixedFamily.ParameterRing M l) q.asIdeal) →
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

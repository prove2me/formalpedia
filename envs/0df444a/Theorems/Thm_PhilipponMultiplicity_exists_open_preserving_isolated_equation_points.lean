-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_isolated_equation_points
-- name    : PhilipponMultiplicity.exists_open_preserving_isolated_equation_points
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-05T15:06:30.017762+00:00
-- url     : https://prove2.me/theorems/e3f679bb-787a-4101-af01-b03541b77c95
-- title:
--   Isolated points of mixed equations persist on an open coefficient neighborhood
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{n_i}$ be the given finite multiprojective space, and let $W\subseteq M$ be closed and irreducible. Fix $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$, and an ordered list $l=(i_0,\ldots,i_{s-1})$ containing each block $i$ exactly $\alpha_i$ times.
--
--   For an array of coefficients $c$, write
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   Z(c)=\{x\in W:P_j(c)(x)=0\text{ for every }j<s\}.
--   $$
--   Choose initial coefficients $c^0$ and a finite subset $S\subseteq Z(c^0)$. Suppose each $x\in S$ has a Zariski-open neighborhood $V_x\subseteq M$ such that $V_x\cap Z(c^0)\subseteq S$.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries, and let $\mathfrak m_c$ be the kernel of evaluation at $c$. There is a Zariski-open subset $U\subseteq\operatorname{Spec}C$ such that
--   $$
--   \mathfrak m_{c^0}\in U,\qquad
--   \mathfrak m_c\in U\ \Longrightarrow\ \text{there is an injection }S\hookrightarrow Z(c).
--   $$
--   Thus the number of prescribed isolated points persists throughout an open neighborhood of the initial coefficient array. Positive-dimensional components away from those points are allowed. The injection need not retain the original points. Empty $S$ and empty equation lists are included.
--
--   **Formalization Note.** This auxiliary incidence-family statement is not a verbatim numbered theorem of the cited sources. The initial rows need not be independent, and no smoothness or global finiteness of the initial section is asserted. An accepted reduction proves that the stated finite-set isolation hypothesis identifies the radical of the actual localized mixed-equation ideal with the localized point-cone ideal, for every nonzero-block representative. It uses homogeneous principal opens, finite-point separation, a point-local projective Nullstellensatz, and primality of the linear point-cone ideal. Its sole Open input is [persistence from this local radical certificate](https://prove2.me/theorems/b3b3c207-d3c1-4690-863e-08a7b53646e9). Construction and comparison of the incidence family, dimension and dominance, and the openness and étale separation argument remain Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the general mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO ; Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32 ; Lemma 29.29.4 (Tag 02FZ), https://stacks.math.columbia.edu/tag/02FZ . Auxiliary synthesis: the incidence variety is a vector bundle over the irreducible W of dimension equal to coefficient-space dimension. A prescribed isolated fibre point forces dominance. Universal openness on the quasi-finite locus and etale separation of finitely many isolated points give an open neighborhood of the initial coefficient point where their number persists. Construction of the incidence scheme, dimension/dominance, and comparison with the concrete point model remain Open. Matrix realization of a given linear section and extraction of a principal open from this neighborhood are proved in the parent reduction.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_isolated_equation_points
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
      (∀ x ∈ S, ∃ V : Set M.Point, @IsOpen _ M.zariskiTopology V ∧ x ∈ V ∧
        V ∩ {x : M.Point | x ∈ W ∧
          ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} ⊆ S) →
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

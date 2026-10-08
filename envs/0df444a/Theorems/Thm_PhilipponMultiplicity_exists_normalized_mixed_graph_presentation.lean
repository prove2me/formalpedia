-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_normalized_mixed_graph_presentation
-- name    : PhilipponMultiplicity.exists_normalized_mixed_graph_presentation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T07:01:03.541774+00:00
-- url     : https://prove2.me/theorems/6d68543f-71ad-42bc-8575-492ce9126aa5
-- title:
--   A normalized graph presentation for a nonempty mixed incidence chart
-- statement:
--   Let $K$ be a base field satisfying the mission's Philippon hypotheses, let $M=\prod_i\mathbf P^{N_i}_K$, and let $W\subset M$ be a closed irreducible locus of dimension $d$. Choose integers $0\leq\alpha_i\leq N_i$ with $\sum_i\alpha_i=d$, and an ordered list $l$ containing factor $i$ exactly $\alpha_i$ times. Put $J=\{0,\ldots,|l|-1\}$ and let $V$ be the set of all homogeneous coordinate indices of $M$. Choose a chart coordinate $b_i$ in each factor and a coordinate polynomial $H$.
--
--   Let $B$ be the universal mixed incidence ring: its equations are the vanishing ideal of $W$, the generic linear equation in factor $l_j$ for each $j\in J$, the normalizations $x_{i,b_i}=1$, and the inverse equation $H z=1$. All coefficient variables indexed by $J\times V$ are retained, including those absent from a particular row. Assume $B$ is nonzero. Define the distinguished coefficient index $p_j=(l_j,b_{l_j})\in V$ and the remaining index set
--
--   $$
--   F=\{(j,v)\in J\times V:v\ne p_j\}.
--   $$
--
--   There exist a finitely generated $K$-algebra $A$ which is an integral domain with $\dim A=d$, and polynomials $g_j\in A[T_f:f\in F]$, such that there is a ring isomorphism
--
--   $$
--   B\;\cong\;
--   A[U_j\ (j\in J),T_f\ (f\in F)]\big/(U_j-g_j(T):j\in J).
--   $$
--
--   This presentation isolates the geometric chart input needed to eliminate one coefficient per incidence row and compute the dimension of the universal incidence ring. The quotient uses the displayed ideal itself; no radical is taken. The assertion is existential in $A$ and in the ring isomorphism, and imposes no compatibility of that isomorphism with the coefficient parameter map.
--
--   The checked reduction now constructs the presentation explicitly using
--   $$
--   A=K[x_{i,t},z]/(I(W),\ x_{i,b_i}-1,\ Hz-1).
--   $$
--   It proves that the substitution maps are inverse for the original incidence ideal, proves finite generation of this ring, and transfers nontriviality from $B$. The outstanding input is [the domain and dimension of this explicit normalized principal chart](p2m:theorem/755cbb9e-0d8f-4938-a70c-ff925e0cc9ba). No coefficient elimination or presentation isomorphism remains in that child.
-- source:
--   Formal auxiliary for the mixed linear-section construction in P. Philippon, “Lemmes de zéros dans les groupes algébriques commutatifs”, Bulletin de la Société Mathématique de France 114 (1986), 355–383, §3, Lemma 3.1 on p. 363 and the mixed-linear-section paragraph on p. 364. https://numdam.org/articles/10.24033/bsmf.2060/ . The graph-presentation statement is an explicit auxiliary for the mission's normalized universal incidence ring, not a verbatim theorem of Philippon. Its intended geometric base is the nonempty principal open of the normalized affine chart of W. For the dimension of a finite-type domain over a field, see Stacks Project, Lemma 10.116.1 (tag 00P0), https://stacks.math.columbia.edu/tag/00P0 . The original equations, pivot normalizations, unused coefficient variables, and inverse equation are specified in the published definition PhilipponMultiplicity_UniversalMixedSlices.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_normalized_mixed_graph_presentation
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        let F := {t : Fin l.length × M.Variable //
          t.2 ≠ (⟨l[t.1], b l[t.1]⟩ : M.Variable)}
        ∃ (A : Type u) (instA : CommRing A) (algA : Algebra K A),
          IsDomain A ∧ Algebra.FiniteType K A ∧
          ringKrullDim A = locusDimension M W ∧
          ∃ g : Fin l.length → MvPolynomial F A,
            Nonempty (MixedFamily.CoordinateRing M W l b H ≃+*
              (MvPolynomial (Fin l.length ⊕ F) A ⧸
                Ideal.span (Set.range (fun j =>
                  (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin l.length ⊕ F) A) -
                    MvPolynomial.rename Sum.inr (g j))))) := by sorry

end PhilipponMultiplicity

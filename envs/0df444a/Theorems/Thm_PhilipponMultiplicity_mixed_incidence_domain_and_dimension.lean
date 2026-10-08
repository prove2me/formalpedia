-- Prove2me | Theorems.Thm_PhilipponMultiplicity_mixed_incidence_domain_and_dimension
-- name    : PhilipponMultiplicity.mixed_incidence_domain_and_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T05:11:59.512526+00:00
-- url     : https://prove2.me/theorems/2388a22e-9e25-47be-922f-71e426406a44
-- title:
--   Domain and expected dimension of a nonempty mixed incidence chart
-- statement:
--   Let $W$ be a closed irreducible subvariety of a multiprojective space $M$ over a Philippon base field $K$, with dimension $d$. Choose integers $0\leq\alpha_i\leq N_i$ whose sum is $d$, and a list $l$ containing each factor $i$ exactly $\alpha_i$ times. Write $J=\{0,\ldots,|l|-1\}$ and let $V$ be the full homogeneous coordinate index set of $M$. Choose one chart coordinate $b_i$ in each factor and a coordinate polynomial $H$.
--
--   Let $B$ be the universal mixed incidence algebra defined by the vanishing ideal of $W$, the generic linear equation for each row of $l$, the normalizations $x_{i,b_i}=1$, and the inverse equation $H z=1$. Its coefficient variables are indexed by all of $J\times V$. If $B$ is nonzero, then
--   $$
--   B\text{ is an integral domain},\qquad \dim B=|J\times V|.
--   $$
--
--   The checked reduction constructs the inverse maps that eliminate a distinguished coefficient from every graph equation, and proves the complementary variable count. Its sole remaining open input is [a normalized graph presentation over an affine domain of dimension $d$](p2m:theorem/6d68543f-71ad-42bc-8575-492ce9126aa5). That child must identify the actual incidence ring with the graph quotient and establish the base chart's dimension in terms of the original Hilbert-polynomial dimension. The exact formal statement and original incidence ideal are unchanged. This is a formal auxiliary for Philippon's mixed-section argument following Lemma 3.1, pp. 363–364.
-- source:
--   P. Philippon, « Lemmes de zéros dans les groupes algébriques commutatifs », Bulletin de la Société Mathématique de France 114 (1986), 355–383, Lemma 3.1 and the following mixed-linear-section paragraph, pp. 363–364; https://numdam.org/articles/10.24033/bsmf.2060/. This auxiliary incidence domain and expected-dimension statement makes explicit the normalized-chart and coefficient-elimination geometry required by the mission's persistence route. For the affine-domain dimension facts used in the surrounding reduction, see Stacks Project, Lemma 10.116.1, Tag 00P0, https://stacks.math.columbia.edu/tag/00P0, and Lemma 10.114.5, Tag 00OT, https://stacks.math.columbia.edu/tag/00OT. Those lemmas do not themselves construct the incidence algebra's chart description or identify its dimension with the mission's Hilbert-polynomial dimension.

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

theorem mixed_incidence_domain_and_dimension
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
        ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
          Nat.card (Fin l.length × M.Variable) := by sorry

end PhilipponMultiplicity

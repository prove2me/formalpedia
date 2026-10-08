-- Prove2me | Theorems.Thm_PhilipponMultiplicity_mixed_finite_model_domain_and_dominance
-- name    : PhilipponMultiplicity.mixed_finite_model_domain_and_dominance
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T03:57:55.626969+00:00
-- url     : https://prove2.me/theorems/7d5792da-5477-424b-9e70-e7125cacc289
-- title:
--   Domain and dominance of a mixed incidence chart with a finite local model
-- statement:
--   Let $W$ be a closed irreducible subvariety of a multiprojective space over a Philippon base field. Choose mixed linear equations whose factor multiplicities sum to $\dim W$. Write $C$ for the polynomial coefficient ring and $B$ for the universal incidence algebra in a normalized principal chart. Its defining equations are the actual vanishing ideal of $W$, the universal mixed rows, the pivot normalizations, and the inverse equation for the chosen chart polynomial.
--
--   Suppose $D\subseteq B$ is finite over $C$ and there is $r\in D$ satisfying
--   $$
--   r\ne0\text{ in }B,\qquad D[1/r]\xrightarrow{\sim}B[1/r]
--   $$
--   under the canonical localization map. Then $B$ is an integral domain and $C\to B$ is injective.
--
--   The checked reduction proves injectivity from equality of the dimensions of $C$ and $B$. A nonzero kernel element would force an integral model to lose a dimension, while the principal localization isomorphism and affine-domain dimension preservation give the reverse inequality. The sole remaining open input is [domain and expected dimension of the nonempty mixed incidence algebra](p2m:theorem/2388a22e-9e25-47be-922f-71e426406a44); this child has no finite-model or dominance hypothesis. The incidence-chart geometry and its comparison with the original Hilbert-polynomial dimension remain to be proved. This is an auxiliary formulation of the mixed-section argument following Philippon's Lemma 3.1, pp. 363–364.
-- source:
--   P. Philippon, « Lemmes de zéros dans les groupes algébriques commutatifs », Bulletin de la Société Mathématique de France 114 (1986), 355–383, Lemma 3.1 and the following mixed-linear-section paragraph, pp. 363–364; https://numdam.org/articles/10.24033/bsmf.2060/. This auxiliary incidence-chart domain and dominance statement makes explicit geometric work needed by the mission's point-persistence route. The finite model hypothesis uses the canonical localization map of a finite subalgebra, as in the algebraic Zariski main theorem, Stacks Project, Theorem 10.123.12, Tag 00Q9, https://stacks.math.columbia.edu/tag/00Q9. The cited Zariski main theorem supplies finite local models; it does not supply the domain or dominance conclusion of this child.

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

theorem mixed_finite_model_domain_and_dominance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
      ∀ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
        Module.Finite (MixedFamily.ParameterRing M l) D →
        ∀ r : D, r.val ≠ 0 →
          Function.Bijective (Localization.awayMap D.val.toRingHom r) →
          IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
          Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
            (MixedFamily.CoordinateRing M W l b H)) := by sorry

end PhilipponMultiplicity

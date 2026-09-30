-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_group_representatives_give_cm_locus
-- name    : PhilipponMultiplicity.regular_group_representatives_give_cm_locus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T11:12:06.924151+00:00
-- url     : https://prove2.me/theorems/d6a52b20-11ce-49d4-99e8-8254b7223126
-- title:
--   Ambient group — the actual open Cohen–Macaulay locus from regular representatives
-- statement:
--   Assume the actual local coordinate ring at each homogeneous representative of G is regular. There is a Zariski-open subset U of the maximal spectrum containing every such representative, whose points on I(G) are exactly actual group representatives, and I(G) is locally Cohen–Macaulay on U in the original regular-sequence definition used by Proposition 3.3. The zero quotient is allowed at points outside V(I(G)). This support lemma isolates the construction of the genuine open locus from the separate proof of group regularity.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), printed pp. 364–365 and 381–382: the ambient group is smooth, so its ideal is perfect at group points before applying Proposition 3.3. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem regular_group_representatives_give_cm_locus
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K)
    (hreg : ∀ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal)))) :
    ∃ U : TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing),
      (∀ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r ∈ U) ∧
      (∀ m ∈ U, G.vanishingIdeal Set.univ ≤ m.asIdeal →
        ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m) ∧
      Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) U := by sorry

end PhilipponMultiplicity

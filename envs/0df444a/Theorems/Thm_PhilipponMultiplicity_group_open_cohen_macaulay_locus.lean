-- Prove2me | Theorems.Thm_PhilipponMultiplicity_group_open_cohen_macaulay_locus
-- name    : PhilipponMultiplicity.group_open_cohen_macaulay_locus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T11:12:11.881659+00:00
-- url     : https://prove2.me/theorems/9083353a-27b4-4bb3-8d37-141341d19e64
-- title:
--   Ambient algebraic group — local Cohen–Macaulayness on the genuine group locus
-- statement:
--   For every embedded product G of commutative algebraic groups over an algebraically closed nontrivially normed field, there is a Zariski-open set U of the maximal spectrum containing all homogeneous group representatives, with every point of U lying on I(G) represented by a genuine group coordinate tuple, and I(G) is locally Cohen–Macaulay on U. The Cohen–Macaulay assertion concerns the actual localized quotient and actual regular sequences, exactly as required by Proposition 3.3 in the proof on p. 382. This theorem adds no regularity hypothesis to the original embedded-group model.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), printed pp. 364–365 and 381–382: the ambient group is smooth, so its ideal is perfect at group points before applying Proposition 3.3. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem group_open_cohen_macaulay_locus
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K) :
    ∃ U : TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing),
      (∀ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r ∈ U) ∧
      (∀ m ∈ U, G.vanishingIdeal Set.univ ≤ m.asIdeal →
        ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m) ∧
      Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) U := by sorry

end PhilipponMultiplicity

-- Prove2me | Theorems.Thm_PhilipponMultiplicity_retainOnGroup_eq_primaryDecomposition
-- name    : PhilipponMultiplicity.retainOnGroup_eq_primaryDecomposition
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T18:41:54.100746+00:00
-- url     : https://prove2.me/theorems/2f4a5b16-8121-4b68-b8e5-907fadcadb3f
-- title:
--   Retention selects precisely the primary components meeting the group
-- statement:
--   For any finite multihomogeneous primary decomposition of an ideal, retention at all genuine homogeneous representatives of group points equals the intersection of exactly those primary components contained in the evaluation maximal ideal of at least one such representative. This identifies the localization definition with Definition 4.2's primary-component prescription. Embedded components and their multiplicities are retained when their support meets the group; the empty intersection is the unit ideal. This holds over every nontrivially normed field.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Definition 4.2 and Proposition 4.3, printed pp. 373–374; https://numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity

theorem PhilipponMultiplicity.retainOnGroup_eq_primaryDecomposition
    (K : Type*) [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)
    (I : Ideal G.CoordinateRing) (D : SectionThreeSupport.PrimaryDecomposition G.ambient I) :
    retainOnGroup G I =
      ⨅ i : {i : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component i ≤ (representativeMaximalIdeal G x).asIdeal}, D.component i.1 := by sorry

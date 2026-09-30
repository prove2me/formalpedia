-- Prove2me | Theorems.Thm_PhilipponMultiplicity_group_has_regular_homogeneous_representative
-- name    : PhilipponMultiplicity.group_has_regular_homogeneous_representative
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T11:12:00.652514+00:00
-- url     : https://prove2.me/theorems/416c24ff-3b89-40a5-9b1e-226251c64aee
-- title:
--   Ambient group — existence of a regular homogeneous representative
-- statement:
--   For every embedded product of commutative algebraic groups over an algebraically closed nontrivially normed field K, some genuine homogeneous representative r has regular local coordinate ring R_m/I(G)R_m. Here R is the original multihomogeneous coordinate ring and m is the kernel of evaluation at the actual coordinate tuple r. Reducedness, a smooth point, and a group representative are all conclusions of the proof, not supplied certificates. This is the generic-point part of the group smoothness input on p. 382.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), printed pp. 364–365 and 381–382: the ambient group is smooth, so its ideal is perfect at group points before applying Proposition 3.3. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem group_has_regular_homogeneous_representative
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K) :
    ∃ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) := by sorry

end PhilipponMultiplicity

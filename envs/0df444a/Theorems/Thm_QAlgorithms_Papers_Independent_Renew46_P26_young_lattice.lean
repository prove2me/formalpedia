-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_young_lattice
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.young_lattice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:03:39.261797+00:00
-- url     : https://prove2.me/theorems/07fe3392-ba10-45cb-9316-f0d78d06dd34
-- title:
--   Unnumbered Young-lattice description
-- statement:
--   View Young diagrams as finite lower ideals of $\mathbb N\times\mathbb N$, ordered by containment; these form a distributive lattice. For diagrams $\mu,\lambda$,
--
--   $$\mu\nearrow\lambda\iff\mu\lessdot\lambda,$$
--
--   where the left side means containment with exactly one added box and the right side is the lattice cover relation. Thus the Young graph is the Hasse diagram of this lattice. Shifting both coordinates by one gives the paper's positive-coordinate convention.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 25, Unnumbered Young-lattice description

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The Young-lattice description (PDF p.25). YoungDiagram already is the
distributive lattice of finite lower ideals of N×N. Its one-box graph is its
Hasse diagram. Coordinates are shifted by one from positive integer coordinates. -/
theorem young_lattice (mu lam : YoungDiagram) : YoungEdge mu lam ↔ mu ⋖ lam := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end

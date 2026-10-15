-- Prove2me | Theorems.Thm_Plasticity_Ext_Brouwer_facets
-- name    : Plasticity.Ext.Brouwer.facets
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:30:44.10904+00:00
-- url     : https://prove2.me/theorems/8fabb9ee-9f82-406a-b2ac-02687ca2b8bf
-- title:
--   Facets of a full grid simplex are its vertex deletions
-- statement:
--   In a Sperner cube of dimension $n=n_1+1$, let $J$ be a grid $n$-simplex and $I$ a list of $n_1+1$ grid points. Then $I$ is a face of $J$ if and only if $I$ is obtained from $J$ by deleting one vertex (keeping the order of the others).
--
--   It is the first counting step of Kuhn's cubical Sperner lemma.
-- source:
--   H. W. Kuhn, IBM J. Res. Dev. 4 (1960); ported from harfe/fixed-point-theorems-lean4 (MIT)

import Definitions.Def_Plasticity_CubicalSperner

namespace Plasticity.Ext.Brouwer
theorem facets (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (J : Fin (SC.n + 1) → SC.G) (hJ : CubicalSperner.simplex SC SC.n J) :
    CubicalSperner.is_face SC I J ↔ ∃ i, I = @CubicalSperner.delete_vertex SC n1 hn1 i J := by sorry
end Plasticity.Ext.Brouwer

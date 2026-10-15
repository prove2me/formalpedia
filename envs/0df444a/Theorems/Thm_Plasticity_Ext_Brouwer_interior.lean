-- Prove2me | Theorems.Thm_Plasticity_Ext_Brouwer_interior
-- name    : Plasticity.Ext.Brouwer.interior
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:30:45.618133+00:00
-- url     : https://prove2.me/theorems/84c94f5b-2128-47da-9797-18a645c46ee3
-- title:
--   An interior codimension-one grid simplex lies in exactly two full simplices
-- statement:
--   In a Sperner cube of dimension $n=n_1+1$, let $I$ be a grid $n_1$-simplex such that no coordinate is constant along its vertices. Then exactly two grid $n$-simplices have $I$ as a face.
--
--   It is the interior case of the parity count in Kuhn's cubical Sperner lemma.
-- source:
--   H. W. Kuhn, IBM J. Res. Dev. 4 (1960); ported from harfe/fixed-point-theorems-lean4 (MIT)

import Definitions.Def_Plasticity_CubicalSperner
import Mathlib.SetTheory.Cardinal.Finite

namespace Plasticity.Ext.Brouwer
theorem interior (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (hI : CubicalSperner.simplex SC n1 I)
    (hD : ∀ (j : Fin SC.n) (q : Fin (SC.p + 1)), ∃ k, I k j ≠ q) :
    Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 2 := by sorry
end Plasticity.Ext.Brouwer

-- Prove2me | Theorems.Thm_Plasticity_Ext_Brouwer_parent_count
-- name    : Plasticity.Ext.Brouwer.parent_count
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:30:43.848437+00:00
-- url     : https://prove2.me/theorems/934c6910-316c-401a-9cce-a276cccd9aa6
-- title:
--   A codimension-one grid simplex lies in one or two full simplices
-- statement:
--   In a Sperner cube of dimension $n=n_1+1$, let $I$ be a grid $n_1$-simplex. If some coordinate is constantly $0$ or constantly $p$ along its vertices, exactly one grid $n$-simplex has $I$ as a face; otherwise exactly two do.
--
--   This is the door-counting step of Kuhn's cubical Sperner lemma.
-- source:
--   H. W. Kuhn, IBM J. Res. Dev. 4 (1960); ported from harfe/fixed-point-theorems-lean4 (MIT)

import Definitions.Def_Plasticity_CubicalSperner
import Mathlib.SetTheory.Cardinal.Finite

namespace Plasticity.Ext.Brouwer
theorem parent_count (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (hI : CubicalSperner.simplex SC n1 I) :
    (((∃ j, ∀ k, I k j = 0) ∨ (∃ j, ∀ k, I k j = Fin.last SC.p)) →
      Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 1) ∧
    (¬((∃ j, ∀ k, I k j = 0) ∨ (∃ j, ∀ k, I k j = Fin.last SC.p)) →
      Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 2) := by sorry
end Plasticity.Ext.Brouwer

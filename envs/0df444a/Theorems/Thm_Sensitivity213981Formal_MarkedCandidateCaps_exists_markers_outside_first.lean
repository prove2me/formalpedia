-- Prove2me | Theorems.Thm_Sensitivity213981Formal_MarkedCandidateCaps_exists_markers_outside_first
-- name    : Sensitivity213981Formal.MarkedCandidateCaps.exists_markers_outside_first
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:28:45.109416+00:00
-- url     : https://prove2.me/theorems/9ff5175a-50b4-432e-bf0c-bf92e1e6d870
-- title:
--   Eligible markers can be chosen outside a target set first
-- statement:
--   Let \(T,E\) be finite sets, and let \(m\le|E|\). There is an \(m\)-element subset \(M\subseteq E\) such that
--   \[
--   |T\cap M|\le\max\{0,m-|E\setminus T|\}.
--   \]
--   This gives the exact overlap correction when selecting eligible markers for a target-prefix cap.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedCandidateCaps.lean, lines 63–102.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.MarkedCandidateCaps.exists_markers_outside_first :
∀ {V : Type} [Fintype.{0} V] [inst : DecidableEq.{1} V] (T E : Finset.{0} V) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@Finset.card.{0} V E)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M E)
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) m)
        (@LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Inter.inter.{0} (Finset.{0} V) (@Finset.instInter.{0} V inst) T M))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
            (@Finset.card.{0} V (@SDiff.sdiff.{0} (Finset.{0} V) (@Finset.instSDiff.{0} V inst) E T))))) := by sorry

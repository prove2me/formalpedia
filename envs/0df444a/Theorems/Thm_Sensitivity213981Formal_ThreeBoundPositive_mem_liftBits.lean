-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits
-- name    : Sensitivity213981Formal.ThreeBoundPositive.mem_liftBits
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:27:09.130286+00:00
-- url     : https://prove2.me/theorems/1668eba8-847e-4192-921a-07dadffab5b6
-- title:
--   Membership in a lifted child-coordinate set
-- statement:
--   Let \(s\) be a finite set of child coordinates and let \(\operatorname{liftBits}(v,c,s)\) embed it into child \(c\) of vertex \(v\). Then
--   \[
--   ((w,e),a)\in\operatorname{liftBits}(v,c,s)
--   \quad\Longleftrightarrow\quad w=v,\ e=c,\ a\in s.
--   \]
--   This identifies the support of a child repair set inside the parent coordinates.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedPositiveBoundary.lean, lines 166–178.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

@[simp]
theorem Sensitivity213981Formal.ThreeBoundPositive.mem_liftBits :
∀ {I V : Type} [Fintype.{0} I] [Fintype.{0} V] (v w : V) (c e : Bool) (a : I) (s : Finset.{0} I),
  Iff
    (@Membership.mem.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (@Finset.instSetLike.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v c s)
      (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w e) a))
    (And (@Eq.{1} V w v)
      (And (@Eq.{1} Bool e c)
        (@Membership.mem.{0, 0} I (Finset.{0} I)
          (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I)) s a))) := by sorry

-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_cover
-- name    : Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_cover
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:32:38.258167+00:00
-- url     : https://prove2.me/theorems/5313641b-2d32-444d-bcd0-c3f0b072c944
-- title:
--   Destroying an ordinary parent either breaks its target or activates a guard
-- statement:
--   Let \(F\) be nested, with \(t_i\le t_j\), \(g_j\le g_i\), and \(q\le q_i\). Suppose a row \(v\) accepts at parameters \((t_j,g_j,q)\). If flipping coordinate \(((w,c),a)\) makes the parent at \((t_i,g_i,q_i)\) false, then either \(w=v\) and the changed child fails target level \(t_i\), or
--   \[
--   R(v,w),\quad \ell(v,w)=c,\quad
--   F_{g_j}(x_{w,c})=\mathrm{false},\quad
--   F_{g_i}(x_{w,c}^{\{a\}})=\mathrm{true}.
--   \]
--   The second alternative is a newly activated failed guard. The theorem gives a two-part cover of every destructive parent flip.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ConditionalOrdinary.lean, lines 226–279.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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

theorem Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_cover :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (ti tj gi gj : L)
  (ht :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (qi q : Nat) (hq : @LE.le.{0} Nat instLENat q qi) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (hv : @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj q x v) (w : V) (c : Bool)
  (a : I)
  (hoff :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi
        (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
          (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
            (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a))))
      Bool.false),
  Or
    (And (@Eq.{1} V w v)
      (@Eq.{1} Bool
        (F ti
          (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)
            (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
        Bool.false))
    (And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
      (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
        (And (@Eq.{1} Bool (F gj (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)) Bool.false)
          (@Eq.{1} Bool
            (F gi
              (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)
                (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
            Bool.true)))) := by sorry

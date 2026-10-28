-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_outgoing_repair
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strict_outgoing_repair
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:43:57.880995+00:00
-- url     : https://prove2.me/theorems/f556d105-36d9-4862-9ff8-8ec0e2964cad
-- title:
--   An outgoing new winner repairs its selected private target child
-- statement:
--   Let p be a zero-tolerance winning row at guard g_j, let p point to v, and suppose g_j≤t_l. If a single flip makes v win with target t_l and guard g_l, the flip belongs to the strict outgoing repair set of p: it changes v’s child selected by the edge p→v from target-false to target-true.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictPositive.lean, lines 99–131.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.strict_outgoing_repair :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (tj gj tl gl : L)
  (hgt :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj tl)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (p v w : V) (c : Bool) (a : I)
  (hp :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x p)
  (hpv : @Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S p v)
  (hv :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tl gl
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v),
  @Membership.mem.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (@Finset.instSetLike.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)))
    (@Sensitivity213981Formal.ThreeBoundConditional.strictOutBits L I V inst_1 inst_2 S F tl gl x p)
    (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a) := by sorry

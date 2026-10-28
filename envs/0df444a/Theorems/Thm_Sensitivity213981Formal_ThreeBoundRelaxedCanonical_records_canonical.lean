-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedCanonical_records_canonical
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedCanonical.records_canonical
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:26.00512+00:00
-- url     : https://prove2.me/theorems/e3570b6a-4696-4a3b-9887-d94b60d1b8fe
-- title:
--   records canonical — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{xs}:\operatorname{List}(\mathbb N),\quad \bigl(\mathit{xs}\in \operatorname{Q3.records}\Longrightarrow \exists \mathit{ss}:\operatorname{List}(\operatorname{Relaxed.State}),\quad \bigl(\bigl(\mathit{xs} = \operatorname{Relaxed.record}\bigl(\mathit{ss}\bigr)\bigr) \land \bigl(\operatorname{Q3.allowedTypes}\bigl(\operatorname{List.map}\bigl(\operatorname{State.kind}, \mathit{ss}\bigr)\bigr) \land \bigl(\operatorname{List.Pairwise}\bigl(\left(a\mapsto \left(b\mapsto \bigl(\operatorname{Q3.orderKey}\bigl(a\bigr) \le \operatorname{Q3.orderKey}\bigl(b\bigr)\bigr)\right)\right), \operatorname{List.map}\bigl(\operatorname{State.kind}, \mathit{ss}\bigr)\bigr) \land \bigl(\bigl(|\mathit{ss}| \le 9\bigr) \land \bigl(\forall s:\operatorname{Relaxed.State},\quad \bigl(s\in \mathit{ss}\Longrightarrow \operatorname{Relaxed.Local}\bigl(|\mathit{ss}|, \operatorname{Relaxed.guardCount}\bigl(\operatorname{List.map}\bigl(\operatorname{State.kind}, \mathit{ss}\bigr)\bigr), s\bigr)\bigr) \land \bigl(\operatorname{Relaxed.Canonical}\bigl(\operatorname{Option.none}, \mathit{ss}\bigr) \land \bigl(\operatorname{Relaxed.weightSum}\bigl(\mathit{ss}\bigr) = \operatorname{Relaxed.target}\bigl(\operatorname{List.map}\bigl(\operatorname{State.kind}, \mathit{ss}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding records canonical step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedOrientation.lean, lines 129–158.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3OrientationTournament
import Definitions.Def_Sensitivity213981Formal_RelaxedCanonical
import Definitions.Def_Sensitivity213981Formal_RelaxedDegreeNecessity
import Definitions.Def_Sensitivity213981Formal_RelaxedOrientation
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRelaxedCanonical.records_canonical :
∀ (xs : List.{0} Nat)
  (hx :
    @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
      Sensitivity213981Formal.ThreeBoundQ3.records xs),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    fun (ss : List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) =>
    And (@Eq.{1} (List.{0} Nat) xs (Sensitivity213981Formal.ThreeBoundRelaxed.record ss))
      (And
        (Sensitivity213981Formal.ThreeBoundQ3.allowedTypes
          (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State Sensitivity213981Formal.ThreeBoundQ3.Kind
            Sensitivity213981Formal.ThreeBoundRelaxed.State.kind ss))
        (And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State Sensitivity213981Formal.ThreeBoundQ3.Kind
              Sensitivity213981Formal.ThreeBoundRelaxed.State.kind ss))
          (And
            (@LE.le.{0} Nat instLENat (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
            (And
              (∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
                @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                    (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
                    (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
                  Sensitivity213981Formal.ThreeBoundRelaxed.Local
                    (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
                    (Sensitivity213981Formal.ThreeBoundRelaxed.guardCount
                      (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                        Sensitivity213981Formal.ThreeBoundQ3.Kind Sensitivity213981Formal.ThreeBoundRelaxed.State.kind
                        ss))
                    s)
              (And
                (Sensitivity213981Formal.ThreeBoundRelaxed.Canonical
                  (@Option.none.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss)
                (@Eq.{1} ((k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) → Int)
                  (Sensitivity213981Formal.ThreeBoundRelaxed.weightSum ss)
                  (Sensitivity213981Formal.ThreeBoundRelaxed.target
                    (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                      Sensitivity213981Formal.ThreeBoundQ3.Kind Sensitivity213981Formal.ThreeBoundRelaxed.State.kind
                      ss)))))))) := by sorry

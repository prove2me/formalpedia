-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_convertedCap_bound
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:30:36.954225+00:00
-- url     : https://prove2.me/theorems/b863c0d9-8ce9-4506-817d-3f208c9ae0b0
-- title:
--   converted Cap bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{caps}:\operatorname{Numeric.Caps},\quad \forall \mathit{perfect}:\mathbb N,\quad \forall r:\operatorname{RankNumeric.Record},\quad \forall e:\mathbb N,\quad \forall q:\mathbb N,\quad \forall a:\mathbb N,\quad \bigl(\bigl(q \le 3\bigr)\Longrightarrow \bigl(\bigl(a \le \bigl(\operatorname{RankNumeric.capPrefix}\bigl(\mathit{caps}, r, q\bigr)-\operatorname{RankNumeric.positivePrefix}\bigl(r, q\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 0\bigr)\Longrightarrow \bigl(\bigl(1 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\operatorname{Caps.pcross}\bigl(\mathit{caps}\bigr)+\operatorname{RankNumeric.allowance}\bigl(1, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 0\bigr)\Longrightarrow \bigl(\bigl(2 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.zero}\bigl(\mathit{caps}\bigr), 2\bigr)+\operatorname{RankNumeric.allowance}\bigl(2, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 0\bigr)\Longrightarrow \bigl(\bigl(3 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\mathit{perfect}+\operatorname{RankNumeric.allowance}\bigl(3, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 1\bigr)\Longrightarrow \bigl(\bigl(3 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.marked}\bigl(\mathit{caps}\bigr), 6\bigr)-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(3, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 2\bigr)\Longrightarrow \bigl(\bigl(4 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.marked}\bigl(\mathit{caps}\bigr), 7\bigr)-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(4, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 3\bigr)\Longrightarrow \bigl(\bigl(5 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.marked}\bigl(\mathit{caps}\bigr), 8\bigr)-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(5, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 3\bigr)\Longrightarrow \bigl(\bigl(6 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.marked}\bigl(\mathit{caps}\bigr), 9\bigr)-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(6, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(q = 3\bigr)\Longrightarrow \bigl(\bigl(7 \le \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\Longrightarrow \bigl(a \le \bigl(\bigl(\operatorname{Caps.at}\bigl(\operatorname{Caps.marked}\bigl(\mathit{caps}\bigr), 11\bigr)-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(7, e, \operatorname{RankNumeric.guardCount}\bigl(r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(a \le \operatorname{RankNumeric.convertedCap}\bigl(\mathit{caps}, \mathit{perfect}, r, e, q\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding converted Cap bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCapData.lean, lines 140–176.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_bound :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (e q a : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hbase :
    @LE.le.{0} Nat instLENat a
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q)
        (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)))
  (hs :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.pcross caps)
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hd :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.zero caps)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (ht :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) perfect
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₁ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₂ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₃ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₄ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₅ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r)))),
  @LE.le.{0} Nat instLENat a (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r e q) := by sorry

-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_negative_weighted
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.negative_weighted
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:30:28.84443+00:00
-- url     : https://prove2.me/theorems/ebca2c16-1097-47cb-95af-47de6bb2560c
-- title:
--   negative weighted — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{caps}:\operatorname{Numeric.Caps},\quad \forall \mathit{perfect}:\mathbb N,\quad \forall r:\operatorname{RankNumeric.Record},\quad \forall e:\mathbb N,\quad \forall q:\mathbb N,\quad \bigl(\bigl(q \le 3\bigr)\Longrightarrow \forall \mathit{count}:\left(\mathbb N\to \mathbb N\right),\quad \forall \mathit{cost}:\left(\mathbb N\to \mathbb N\right),\quad \bigl(\forall k:\mathbb N,\quad \bigl(\bigl(k \le q\bigr)\Longrightarrow \bigl(\sum_{b\in \operatorname{Finset.range}\bigl(\bigl(k+1\bigr)\bigr)} \mathit{count}\bigl(b\bigr) \le \operatorname{RankNumeric.convertedCap}\bigl(\mathit{caps}, \mathit{perfect}, r, e, k\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall k:\mathbb N,\quad \bigl(\bigl(\bigl(k+1\bigr) \le q\bigr)\Longrightarrow \bigl(\mathit{cost}\bigl(\bigl(k+1\bigr)\bigr) \le \mathit{cost}\bigl(k\bigr)\bigr)\bigr)\Longrightarrow \bigl(\sum_{b\in \operatorname{Finset.range}\bigl(\bigl(q+1\bigr)\bigr)} \bigl(\mathit{count}\bigl(b\bigr)\cdot \mathit{cost}\bigl(b\bigr)\bigr) \le \operatorname{List.sum}\bigl(\operatorname{List.map}\bigl(\left(b\mapsto \bigl(\operatorname{RankNumeric.negativeCount}\bigl(\mathit{caps}, \mathit{perfect}, q, r, e, b\bigr)\cdot \mathit{cost}\bigl(b\bigr)\bigr)\right), \operatorname{List.range}\bigl(\bigl(q+1\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding negative weighted step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankNegativeGreedy.lean, lines 15–64.

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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.negative_weighted :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (e q : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (count cost : Nat → Nat)
  (hp :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat k q →
        @LE.le.{0} Nat instLENat
          (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
            (Finset.range
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            fun (b : Nat) => count b)
          (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r e k))
  (ha :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          q →
        @LE.le.{0} Nat instLENat
          (cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (cost k)),
  @LE.le.{0} Nat instLENat
    (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (b : Nat) => @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (count b) (cost b))
    (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
      (@List.map.{0, 0} Nat Nat
        (fun (b : Nat) =>
          @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (Sensitivity213981Formal.ThreeBoundRankNumeric.negativeCount caps perfect q r e b) (cost b))
        (List.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by sorry

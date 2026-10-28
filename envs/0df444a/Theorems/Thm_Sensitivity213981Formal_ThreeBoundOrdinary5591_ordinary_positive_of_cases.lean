-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_ordinary_positive_of_cases
-- name    : Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinary_positive_of_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:36.345343+00:00
-- url     : https://prove2.me/theorems/31387e6a-619e-4fe2-8ad6-e89b54cc4911
-- title:
--   ordinary positive of cases — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall k:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall T:\operatorname{Paper320.Tournament}\bigl(k\bigr),\quad \forall \mathit{label}:\left(\{0,\ldots,k-1\}\to \left(\{0,\ldots,k-1\}\to \{0,\ldots,2-1\}\right)\right),\quad \bigl(\operatorname{Ordinary5591.LabelCaps}\bigl(T, \mathit{label}\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Paper320.NestedFamily}\bigl(F\bigr)\Longrightarrow \forall \mathit{ta}:\{0,\ldots,n-1\},\quad \forall \mathit{tb}:\{0,\ldots,n-1\},\quad \forall \mathit{ga}:\{0,\ldots,n-1\},\quad \forall \mathit{gb}:\{0,\ldots,n-1\},\quad \bigl(\bigl(\mathit{ta} \le \mathit{tb}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gb} \le \mathit{ga}\bigr)\Longrightarrow \bigl(\bigl(\mathit{ga} \le \mathit{ta}\bigr)\Longrightarrow \forall \mathit{qa}:\mathbb N,\quad \forall q:\mathbb N,\quad \bigl(\bigl(q \le \mathit{qa}\bigr)\Longrightarrow \bigl(\bigl(4 \le q\bigr)\Longrightarrow \bigl(\bigl(q \le 8\bigr)\Longrightarrow \forall a:\mathbb N,\quad \forall b:\mathbb N,\quad \forall s:\mathbb N,\quad \forall j:\mathbb N,\quad \forall z:\mathbb N,\quad \bigl(\bigl(j \le s\bigr)\Longrightarrow \bigl(\operatorname{ZT.PBound}\bigl(F, \mathit{gb}, \mathit{ta}, \mathit{tb}, a\bigr)\Longrightarrow \bigl(\operatorname{ZT.ABound}\bigl(F, \mathit{gb}, \mathit{tb}, b\bigr)\Longrightarrow \bigl(\operatorname{ZT.BBound}\bigl(F, \mathit{gb}, \mathit{ga}, s\bigr)\Longrightarrow \bigl(\operatorname{ZT.BBound}\bigl(F, \mathit{gb}, \mathit{tb}, j\bigr)\Longrightarrow \bigl(\forall m:\mathbb N,\quad \forall u:\mathbb N,\quad \bigl(\bigl(m \le \operatorname{ite}\bigl(\bigl(\mathit{qa} = q\bigr), \bigl(\bigl(2\cdot q\bigr)+3\bigr), 0\bigr)\bigr)\Longrightarrow \bigl(\bigl(u \le \bigl(\bigl(2\cdot q\bigr)+1\bigr)\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Nat.choose}\bigl(\bigl(u+m\bigr), 2\bigr) \le \bigl(\bigl(q\cdot u\bigr)+\bigl(\bigl(q+1\bigr)\cdot m\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(u \le \operatorname{Ordinary5591.candidateTotalCap}\bigl(q, m, u\bigr)\bigr)\Longrightarrow \bigl(\bigl(\bigl(0 < u\bigr)\Longrightarrow \bigl(\mathit{gb} \ne \mathit{ta}\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Ordinary5591.positiveCaseCost}\bigl(q, m, u, a, b, s, j\bigr) \le z\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\Longrightarrow \forall x:\left(\{0,\ldots,k-1\}\times \{0,\ldots,2-1\}\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Sensitivity2075.tolerantFamily}\bigl(T, \mathit{label}, F, \mathit{ta}, \mathit{ga}, \mathit{qa}, x\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(|\operatorname{ZT.flipsTo}\bigl(\operatorname{Sensitivity2075.tolerantFamily}\bigl(T, \mathit{label}, F, \mathit{tb}, \mathit{gb}, q\bigr), \mathsf{true}, x\bigr)| \le z\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding ordinary positive of cases step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Ordinary5591Caps.lean, lines 135–184.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinary_positive_of_cases :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I]
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hCaps : @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps k T label) (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (ta tb ga gb : Fin n)
  (ht : @LE.le.{0} (Fin n) (@instLEFin n) ta tb) (hg : @LE.le.{0} (Fin n) (@instLEFin n) gb ga)
  (hga : @LE.le.{0} (Fin n) (@instLEFin n) ga ta) (qa q : Nat) (hq : @LE.le.{0} Nat instLENat q qa)
  (hlarge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
  (hq8 : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (a b s j z : Nat)
  (hjs : @LE.le.{0} Nat instLENat j s)
  (ha : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.PBound I inst n F gb ta tb a)
  (hb : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.ABound I inst n F gb tb b)
  (hs : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb ga s)
  (hj : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb tb j)
  (hcases :
    ∀ (m u : Nat),
      @LE.le.{0} Nat instLENat m
          (@ite.{1} Nat (@Eq.{1} Nat qa q) (instDecidableEqNat qa q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
        @LE.le.{0} Nat instLENat u
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          @LE.le.{0} Nat instLENat
              (Nat.choose (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u m)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q u)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m)) →
            @LE.le.{0} Nat instLENat u (Sensitivity213981Formal.ThreeBoundOrdinary5591.candidateTotalCap q m u) →
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u →
                  @Ne.{1} (Fin n) gb ta) →
                @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundOrdinary5591.positiveCaseCost q m u a b s j)
                  z)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F ta ga qa x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0}
      (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.flipsTo
        (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
        (@instFintypeProd.{0, 0}
          (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I
          (@instFintypeProd.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype k) (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          inst)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb gb q)
        Bool.true x))
    z := by sorry

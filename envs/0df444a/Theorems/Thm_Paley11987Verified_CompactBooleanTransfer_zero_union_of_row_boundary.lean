-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_zero_union_of_row_boundary
-- name    : Paley11987Verified.CompactBooleanTransfer.zero_union_of_row_boundary
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:03:25.553325+00:00
-- url     : https://prove2.me/theorems/2f495d4c-f456-435f-932b-07ce1ddd292d
-- title:
--   A zero-tolerance union bound from row boundaries
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Let $T$ have constant outdegree $d$. Choose target levels $t_i\le t_j\le t_k\le t_l$ and guard levels $g_l\le g_k\le g_j\le g_i$, with $g_i\le t_l$ and $g_l\le t_i$. Assume child bounds
--   $$\mathcal B(F;t_i,t_l;b),\quad\mathcal A(F;g_l,g_i;a),\quad
--   \mathcal D(F;t_i,t_j,t_k,t_l;d_t),\quad\mathcal D(F;g_l,g_k,g_j,g_i;d_g).$$
--   At an input $x$, suppose $H_{t_j,g_j,0}(x)=1$ and $H_{t_k,g_k,0}(x)=0$. Whenever a row changes from true at $(t_j,g_j)$ to false at $(t_k,g_k)$, require its $(t_i,g_i)$ false-flip boundary to have size at most $R$. Then
--   $$|U_0(H_{t_i,g_i,0},x)\cup U_1(H_{t_l,g_l,0},x)|\le
--   \max\!\left\{R,
--   \begin{cases}b+da+d_t&t_j<t_k\\0&t_j=t_k\end{cases},
--   \begin{cases}2b+(d\mathbin{\ominus}1)a+d_g&g_k<g_j\\0&g_k=g_j\end{cases}\right\}.$$
--   All costs are natural numbers. This supplies the four-level union estimate used by the D-profile transfer.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferZeroUnion, SHA256 21516db7f0aa96f6349b508616d74053c3d54d2fbaa404319007271696513858; compact solution lines 9929-10046, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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
import Definitions.Def_Paley11987Support_020

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.zero_union_of_row_boundary :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool),
  @OAI.Paper320.NestedFamily n I F →
    ∀ (ti tj tk tl gi gj gk gl : Fin n),
      @LE.le.{0} (Fin n) (@instLEFin n) ti tj →
        @LE.le.{0} (Fin n) (@instLEFin n) tj tk →
          @LE.le.{0} (Fin n) (@instLEFin n) tk tl →
            @LE.le.{0} (Fin n) (@instLEFin n) gj gi →
              @LE.le.{0} (Fin n) (@instLEFin n) gk gj →
                @LE.le.{0} (Fin n) (@instLEFin n) gl gk →
                  @LE.le.{0} (Fin n) (@instLEFin n) gi tl →
                    @LE.le.{0} (Fin n) (@instLEFin n) gl ti →
                      ∀ (d : Nat),
                        (∀ (v : Fin k),
                            @Eq.{1} Nat
                              (@Finset.card.{0} (Fin k)
                                (@Finset.filter.{0} (Fin k)
                                  (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) v)
                                  (fun a =>
                                    Classical.propDecidable
                                      (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) v a))
                                  (@Finset.univ.{0} (Fin k) (Fin.fintype k))))
                              d) →
                          ∀ (b a dt dg R : Nat),
                            @ZT.BBound I inst n F ti tl b →
                              @ZT.ABound I inst n F gl gi a →
                                @ZT.DBound I inst n F ti tj tk tl dt →
                                  @ZT.DBound I inst n F gl gk gj gi dg →
                                    ∀
                                      (x :
                                        Prod.{0, 0}
                                            (Prod.{0, 0} (Fin k)
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                            I →
                                          Bool),
                                      @Eq.{1} Bool
                                          (@Sensitivity2075.tolerantFamily n k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tj
                                            gj (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                                          Bool.true →
                                        @Eq.{1} Bool
                                            (@Sensitivity2075.tolerantFamily n k
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F
                                              tk gk (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                                            Bool.false →
                                          (∀ (v : Fin k),
                                              @Eq.{1} Bool
                                                  (@Sensitivity2075.tolerantRow n k
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T
                                                    label F tj gj
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v)
                                                  Bool.true →
                                                @Eq.{1} Bool
                                                    (@Sensitivity2075.tolerantRow n k
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T
                                                      label F tk gk
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v)
                                                    Bool.false →
                                                  @LE.le.{0} Nat instLENat
                                                    (@Finset.card.{0}
                                                      (Prod.{0, 0}
                                                        (Prod.{0, 0} (Fin k)
                                                          (Fin
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))))
                                                        I)
                                                      (@ZT.flipsTo
                                                        (Prod.{0, 0}
                                                          (Prod.{0, 0} (Fin k)
                                                            (Fin
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))))
                                                          I)
                                                        (@instFintypeProd.{0, 0}
                                                          (Prod.{0, 0} (Fin k)
                                                            (Fin
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))))
                                                          I
                                                          (@instFintypeProd.{0, 0} (Fin k)
                                                            (Fin
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2))))
                                                            (Fin.fintype k)
                                                            (Fin.fintype
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))))
                                                          inst)
                                                        (fun y =>
                                                          @Sensitivity2075.tolerantRow n k
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            I T label F ti gi
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                              (instOfNatNat (nat_lit 0)))
                                                            y v)
                                                        Bool.false x))
                                                    R) →
                                            @LE.le.{0} Nat instLENat
                                              (@Finset.card.{0}
                                                (Prod.{0, 0}
                                                  (Prod.{0, 0} (Fin k)
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                                  I)
                                                (@Union.union.{0}
                                                  (Finset.{0}
                                                    (Prod.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I))
                                                  (@Finset.instUnion.{0}
                                                    (Prod.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I)
                                                    fun a b =>
                                                    @instDecidableEqProd.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I
                                                      (fun a b =>
                                                        @instDecidableEqProd.{0, 0} (Fin k)
                                                          (Fin
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (instDecidableEqFin k)
                                                          (instDecidableEqFin
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          a b)
                                                      (fun a b => Classical.propDecidable (@Eq.{1} I a b)) a b)
                                                  (@ZT.flipsTo
                                                    (Prod.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I)
                                                    (@instFintypeProd.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I
                                                      (@instFintypeProd.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (Fin.fintype k)
                                                        (Fin.fintype
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      inst)
                                                    (@Sensitivity2075.tolerantFamily n k
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T
                                                      label F ti gi
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                    Bool.false x)
                                                  (@ZT.flipsTo
                                                    (Prod.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I)
                                                    (@instFintypeProd.{0, 0}
                                                      (Prod.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      I
                                                      (@instFintypeProd.{0, 0} (Fin k)
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (Fin.fintype k)
                                                        (Fin.fintype
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      inst)
                                                    (@Sensitivity2075.tolerantFamily n k
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T
                                                      label F tl gl
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                    Bool.true x)))
                                              (@Max.max.{0} Nat Nat.instMax R
                                                (@Max.max.{0} Nat Nat.instMax
                                                  (@ite.{1} Nat (@LT.lt.{0} (Fin n) (@instLTFin n) tj tk)
                                                    (@Fin.decLt n tj tk)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          d a))
                                                      dt)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@ite.{1} Nat (@LT.lt.{0} (Fin n) (@instLTFin n) gk gj)
                                                    (@Fin.decLt n gk gj)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                            (@instHSub.{0} Nat instSubNat) d
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          a))
                                                      dg)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by sorry

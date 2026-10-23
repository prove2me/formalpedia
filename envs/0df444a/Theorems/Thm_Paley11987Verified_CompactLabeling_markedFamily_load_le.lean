-- Prove2me | Theorems.Thm_Paley11987Verified_CompactLabeling_markedFamily_load_le
-- name    : Paley11987Verified.CompactLabeling.markedFamily_load_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:28:55.190291+00:00
-- url     : https://prove2.me/theorems/8300f902-618a-408a-b719-73265555fdae
-- title:
--   Coordinate load of marked labeling events
-- statement:
--   Let $R$ be an irreflexive tournament on $n$ vertices, with every indegree equal to $d$ and every pair of distinct vertices having $c$ common in-neighbors. Fix natural parameters $q,a,m,B$. Write $P_t(k)$ for the row-pattern count, $w(f)$ for the orientation weight determined by $q$ and coefficients $C_t$, and $E$ for the recorded head-error factor for $q,a,m,B$.
--
--   Let $u,w_m,W,\lambda,\gamma$ be nonnegative rationals, let $\alpha,\beta$ be rationals, and assume $C_t\ge0$ for $t\le q$. Require
--   $$P_t(k)\le C_tu^k\ (k<a,\ t\le q),\qquad
--   w(f)\le\alpha+\beta f+\gamma\binom f2,\quad w(f)\le w_m\ (f\le m),$$
--   $$W=\alpha(n-m)+\beta\left(md-\binom m2\right)+\gamma\binom m2c.$$
--   For any coordinate $e$, summing the local probabilities $p_I$ of marked bad events whose supports contain $e$ gives
--   $$\frac12\sum_{I:e\in S_I}p_I\lambda^{\binom a2+ma}
--   \le\frac{2^aEu^{\binom a2}}{2^{\binom a2+ma}}
--   \left[\binom nm w_m^2\frac{W^{a\mathbin{\ominus}2}}{(a\mathbin{\ominus}2)!}
--   +\binom n{m\mathbin{\ominus}1}w_m\frac{W^{a\mathbin{\ominus}1}}{(a\mathbin{\ominus}1)!}\right]
--   \frac{\lambda^{\binom a2+ma}}2.$$
--   Natural subtraction in the exponents and binomial indices is truncated at zero. This estimate supplies the marked-event part of the coordinate budget.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingMarkedFamilyBound, SHA256 5352f107b37e2e1c192bc2bd23a49dd5afc0cafa6c8d90a1811a6cdd2703b1fd; compact solution lines 3185-3238, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_013

set_option autoImplicit false
set_option Elab.async false
universe u_1

theorem Paley11987Verified.CompactLabeling.markedFamily_load_le :
∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V] (R : V → V → Prop) (n deg c : Nat),
  @Eq.{1} Nat (@Fintype.card.{u_1} V inst) n →
    (∀ (x : V), Not (R x x)) →
      (∀ (x y : V), @Ne.{u_1 + 1} V x y → Iff (R x y) (Not (R y x))) →
        (∀ (y : V), @Eq.{1} Nat (@Finset.card.{u_1} V (@ZL.inOn.{u_1} V R (@Finset.univ.{u_1} V inst) y)) deg) →
          (∀ (x y : V),
              @Ne.{u_1 + 1} V x y →
                @Eq.{1} Nat
                  (@Finset.card.{u_1} V
                    (@Finset.filter.{u_1} V (fun z => And (R z x) (R z y))
                      (fun a =>
                        @instDecidableAnd (R a x) (R a y) (Classical.propDecidable (R a x))
                          (Classical.propDecidable (R a y)))
                      (@Finset.univ.{u_1} V inst)))
                  c) →
            ∀ (q a m B : Nat) (u : Rat) (C : Nat → Rat) (α β γ wm W lam : Rat),
              @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) u →
                (∀ (t : Nat),
                    @LE.le.{0} Nat instLENat t q →
                      @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (C t)) →
                  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) γ →
                    @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) wm →
                      @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) W →
                        @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) lam →
                          (∀ (k : Nat),
                              @LT.lt.{0} Nat instLTNat k a →
                                ∀ (t : Nat),
                                  @LE.le.{0} Nat instLENat t q →
                                    @LE.le.{0} Rat Rat.instLE
                                      (@Nat.cast.{0} Rat Rat.instNatCast (ZL.RowCounting.rowPatterns t k))
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (C t)
                                        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) u
                                          k))) →
                            (∀ (f : Nat),
                                @LE.le.{0} Nat instLENat f m →
                                  @LE.le.{0} Rat Rat.instLE (ZL.orientationWeight q C f)
                                    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) α
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) β
                                          (@Nat.cast.{0} Rat Rat.instNatCast f)))
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) γ
                                        (@Nat.cast.{0} Rat Rat.instNatCast
                                          (f.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) →
                              (∀ (f : Nat),
                                  @LE.le.{0} Nat instLENat f m →
                                    @LE.le.{0} Rat Rat.instLE (ZL.orientationWeight q C f) wm) →
                                @Eq.{1} Rat W
                                    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) α
                                          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                            (@Nat.cast.{0} Rat Rat.instNatCast n)
                                            (@Nat.cast.{0} Rat Rat.instNatCast m)))
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) β
                                          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                              (@Nat.cast.{0} Rat Rat.instNatCast m)
                                              (@Nat.cast.{0} Rat Rat.instNatCast deg))
                                            (@Nat.cast.{0} Rat Rat.instNatCast
                                              (m.choose
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) γ
                                          (@Nat.cast.{0} Rat Rat.instNatCast
                                            (m.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                        (@Nat.cast.{0} Rat Rat.instNatCast c))) →
                                  ∀ (x y : V),
                                    @LE.le.{0} Rat Rat.instLE
                                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                        (@Finset.sum.{u_1, 0} (@ZL.MarkedIndex.{u_1} V inst inst_1 a m) Rat
                                          Rat.addCommMonoid
                                          (@Finset.filter.{u_1} (@ZL.MarkedIndex.{u_1} V inst inst_1 a m)
                                            (fun I =>
                                              @Membership.mem.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                                (Finset.{u_1} (Prod.{u_1, u_1} V V))
                                                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Prod.{u_1, u_1} V V))
                                                  (Prod.{u_1, u_1} V V)
                                                  (@Finset.instSetLike.{u_1} (Prod.{u_1, u_1} V V)))
                                                (@ZL.SupportedFamily.support.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                                  (@ZL.MarkedIndex.{u_1} V inst inst_1 a m)
                                                  (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                                  (@ZL.markedFamily.{u_1} V inst inst_1 R q a m B) I)
                                                (@Prod.mk.{u_1, u_1} V V x y))
                                            (fun a_1 =>
                                              @Finset.decidableMem.{u_1} (Prod.{u_1, u_1} V V)
                                                (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                                (@Prod.mk.{u_1, u_1} V V x y)
                                                (@ZL.SupportedFamily.support.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                                  (@ZL.MarkedIndex.{u_1} V inst inst_1 a m)
                                                  (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                                  (@ZL.markedFamily.{u_1} V inst inst_1 R q a m B) a_1))
                                            (@Finset.univ.{u_1} (@ZL.MarkedIndex.{u_1} V inst inst_1 a m)
                                              (@ZL.markedIndexFintype.{u_1} V inst inst_1 a m)))
                                          fun I =>
                                          @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                            (@ZL.SupportedFamily.localProbability.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                              (@ZL.MarkedIndex.{u_1} V inst inst_1 a m)
                                              (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                              (@ZL.markedFamily.{u_1} V inst inst_1 R q a m B) I)
                                            (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                              lam
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a))))
                                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                    (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                                    (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) a)
                                                  (@Nat.cast.{0} Rat Rat.instNatCast (ZL.headErrorFactor q a m B)))
                                                (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                  (@instHPow.{0, 0} Rat Nat Rat.instPowNat) u
                                                  (a.choose
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                              (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                                (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (a.choose
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
                                                    a))))
                                            (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                  (@Nat.cast.{0} Rat Rat.instNatCast (n.choose m))
                                                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                    (@instHPow.{0, 0} Rat Nat
                                                      (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
                                                    wm (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                    (@instHPow.{0, 0} Rat Nat Rat.instPowNat) W
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                                  (@Nat.cast.{0} Rat Rat.instNatCast
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                          (instOfNatNat (nat_lit 2)))).factorial)))
                                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                                  (@Nat.cast.{0} Rat Rat.instNatCast
                                                    (n.choose
                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                  wm)
                                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                    (@instHPow.{0, 0} Rat Nat Rat.instPowNat) W
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (@Nat.cast.{0} Rat Rat.instNatCast
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1)))).factorial)))))
                                          (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                            lam
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a))))
                                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))) := by sorry

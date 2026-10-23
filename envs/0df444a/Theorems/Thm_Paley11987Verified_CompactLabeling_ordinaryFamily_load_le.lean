-- Prove2me | Theorems.Thm_Paley11987Verified_CompactLabeling_ordinaryFamily_load_le
-- name    : Paley11987Verified.CompactLabeling.ordinaryFamily_load_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:26:33.035751+00:00
-- url     : https://prove2.me/theorems/b0776786-ee72-4977-bf88-9f84cc5acd1b
-- title:
--   Coordinate load of ordinary labeling events
-- statement:
--   Let $R$ be an irreflexive tournament on a finite set $V$ of size $n$. Fix natural numbers $q,a,l,r,L,H$ with $r\le a$, $L,H>0$, and $la+r=\binom a2$. Let $\lambda\in\mathbb Q_{\ge0}$ and let $P_q(d)$ be the number of allowed row patterns. Assume
--   $$P_q(d)L^dH^l\le L^{l+1}H^d\qquad(0\le d<a).$$
--   For an ordinary bad event $I$ of size $a$, let $S_I$ be its coordinate support and $p_I$ its local probability. For every ordered coordinate $e=(x,y)\in V^2$,
--   $$\frac12\sum_{I:e\in S_I}p_I\lambda^{\binom a2}\le
--   \binom n{a\mathbin{\ominus}2}\frac{2^a L^{a-r}H^r}{2^{\binom a2}}\frac{\lambda^{\binom a2}}2.$$
--   Here $u\mathbin{\ominus}v=\max(u-v,0)$. The sum ranges over the ordinary event family specified by $R,q,a$. This bound controls the ordinary contribution to the local-lemma coordinate budget.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingOrdinaryFamilyBound, SHA256 3a466d542db4579653d07bd9a2ffdeaf3f4cdc9f76576c57f9b080a4570e28af; compact solution lines 2948-2998, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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

theorem Paley11987Verified.CompactLabeling.ordinaryFamily_load_le :
∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V] (R : V → V → Prop) (n : Nat),
  @Eq.{1} Nat (@Fintype.card.{u_1} V inst) n →
    (∀ (x : V), Not (R x x)) →
      (∀ (x y : V), @Ne.{u_1 + 1} V x y → Iff (R x y) (Not (R y x))) →
        ∀ (q a lo rem L H : Nat) (lam : Rat),
          @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) lam →
            @LE.le.{0} Nat instLENat rem a →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) L →
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) H →
                  @Eq.{1} Nat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) lo a) rem)
                      (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    (∀ (d : Nat),
                        @LT.lt.{0} Nat instLTNat d a →
                          @LE.le.{0} Nat instLENat
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (ZL.RowCounting.rowPatterns q d)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  L d))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                H lo))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                L
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) lo
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                H d))) →
                      ∀ (x y : V),
                        @LE.le.{0} Rat Rat.instLE
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@Finset.sum.{u_1, 0}
                              (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                  (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V)) (Finset.{u_1} V)
                                    (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                  (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                              Rat Rat.addCommMonoid
                              (@Finset.filter.{u_1}
                                (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                  @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                    (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V)) (Finset.{u_1} V)
                                      (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                    (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                                (fun I =>
                                  @Membership.mem.{u_1, u_1} (Prod.{u_1, u_1} V V) (Finset.{u_1} (Prod.{u_1, u_1} V V))
                                    (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Prod.{u_1, u_1} V V))
                                      (Prod.{u_1, u_1} V V) (@Finset.instSetLike.{u_1} (Prod.{u_1, u_1} V V)))
                                    (@ZL.SupportedFamily.support.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                      (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                        @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V))
                                            (Finset.{u_1} V) (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                          (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                                      (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                      (@ZL.ordinaryFamily.{u_1} V inst inst_1 R q a) I)
                                    (@Prod.mk.{u_1, u_1} V V x y))
                                (fun a_1 =>
                                  @Finset.decidableMem.{u_1} (Prod.{u_1, u_1} V V)
                                    (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                    (@Prod.mk.{u_1, u_1} V V x y)
                                    (@ZL.SupportedFamily.support.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                      (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                        @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V))
                                            (Finset.{u_1} V) (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                          (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                                      (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                      (@ZL.ordinaryFamily.{u_1} V inst inst_1 R q a) a_1))
                                (@Finset.univ.{u_1}
                                  (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                    @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V))
                                        (Finset.{u_1} V) (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                      (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                                  (@ZL.ordinaryIndexFintype.{u_1} V inst inst_1 a)))
                              fun I =>
                              @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                (@ZL.SupportedFamily.localProbability.{u_1, u_1} (Prod.{u_1, u_1} V V)
                                  (@Subtype.{u_1 + 1} (Finset.{u_1} V) fun x =>
                                    @Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
                                      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} V))
                                        (Finset.{u_1} V) (@Finset.instSetLike.{u_1} (Finset.{u_1} V)))
                                      (@ZL.OrdinaryIndex.{u_1} V inst inst_1 a) x)
                                  (fun a b => @instDecidableEqProd.{u_1, u_1} V V inst_1 inst_1 a b)
                                  (@ZL.ordinaryFamily.{u_1} V inst inst_1 R q a) I)
                                (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) lam
                                  (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                (@Nat.cast.{0} Rat Rat.instNatCast
                                  (n.choose
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                  (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                    (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) a)
                                    (@Nat.cast.{0} Rat Rat.instNatCast
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          L (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a rem))
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          H rem))))
                                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                    (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                    (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) lam
                                (a.choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))) := by sorry

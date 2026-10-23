-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_ordinary_zero_tolerance
-- name    : Paley11987Verified.CompactBooleanTransfer.ordinary_zero_tolerance
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:55:31.815664+00:00
-- url     : https://prove2.me/theorems/b8afe999-b71e-4822-bb07-9996719c81f6
-- title:
--   Ordinary zero-tolerance transfer
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Choose levels $t_a\le t_b$, $g_b\le g_a\le t_a$ and natural costs $a,b,s,j,d$ with $j\le s$. Suppose the child bounds are
--   $$\mathcal P(F;g_b,t_a,t_b;a),\quad\mathcal A(F;g_b,t_b;b),\quad
--   \mathcal B(F;g_b,g_a;s),\quad\mathcal B(F;g_b,t_b;j),\quad
--   \mathcal D(F;g_b,g_a,t_a,t_b;d).$$
--   Assume the binary labeling has ordinary defect cap $24$ at tolerance zero, source cap $22$, and double-dominator cap $18$, in the precise exclusion senses of the interface. Then, whenever $H_{t_a,g_a,0}(x)=0$,
--   $$|U_1(H_{t_b,g_b,0},x)|\le Z_0(a,b,s,j,d),$$
--   where $Z_0$ is the explicit zero-tolerance cost function. This handles the zero-tolerance branch without requiring the full positive-tolerance labeling-cap hypothesis.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferZeroStage, SHA256 ee0edbeba2de9c6593dd177d6c7c31f2c3b09f60bae57768d4b04cc5fef879ed; compact solution lines 9092-9141, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_041

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.ordinary_zero_tolerance :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool),
  @OAI.Paper320.NestedFamily n I F →
    ∀ (ta tb ga gb : Fin n),
      @LE.le.{0} (Fin n) (@instLEFin n) ta tb →
        @LE.le.{0} (Fin n) (@instLEFin n) gb ga →
          @LE.le.{0} (Fin n) (@instLEFin n) ga ta →
            ∀ (a b s j d : Nat),
              @LE.le.{0} Nat instLENat j s →
                @ZT.PBound I inst n F gb ta tb a →
                  @ZT.ABound I inst n F gb tb b →
                    @ZT.BBound I inst n F gb ga s →
                      @ZT.BBound I inst n F gb tb j →
                        @ZT.DBound I inst n F gb ga ta tb d →
                          @SensitivityQ.DefectBound k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) T
                              label (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) →
                            @SensitivitySourceZero.SourceBound k
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) T label
                                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
                              @ZT.DoubleCardBound k T label
                                  (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
                                ∀
                                  (x :
                                    Prod.{0, 0}
                                        (Prod.{0, 0} (Fin k)
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                        I →
                                      Bool),
                                  @Eq.{1} Bool
                                      (@Sensitivity2075.tolerantFamily n k
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F ta ga
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                                      Bool.false →
                                    @LE.le.{0} Nat instLENat
                                      (@Finset.card.{0}
                                        (Prod.{0, 0}
                                          (Prod.{0, 0} (Fin k)
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                          I)
                                        (@ZT.flipsTo
                                          (Prod.{0, 0}
                                            (Prod.{0, 0} (Fin k)
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                            I)
                                          (@instFintypeProd.{0, 0}
                                            (Prod.{0, 0} (Fin k)
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                            I
                                            (@instFintypeProd.{0, 0} (Fin k)
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin.fintype k)
                                              (Fin.fintype
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                            inst)
                                          (@Sensitivity2075.tolerantFamily n k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb
                                            gb (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          Bool.true x))
                                      (ZT.zeroCost a b s j d) := by sorry

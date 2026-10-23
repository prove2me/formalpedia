-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_ordinary_positive_of_cases
-- name    : Paley11987Verified.CompactBooleanTransfer.ordinary_positive_of_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:48:27.121342+00:00
-- url     : https://prove2.me/theorems/1002bbbd-7afd-4127-ad74-cd9d54430adb
-- title:
--   Positive-tolerance transfer from finite case costs
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Assume binary labels satisfy the labeling caps. Choose levels $t_a\le t_b$ and $g_b\le g_a\le t_a$, tolerances $q\le q_a$ with $1\le q\le8$, and natural costs $a,b,s,j,z$ with $j\le s$. Assume the child bounds
--   $$\mathcal P(F;g_b,t_a,t_b;a),\quad\mathcal A(F;g_b,t_b;b),\quad
--   \mathcal B(F;g_b,g_a;s),\quad\mathcal B(F;g_b,t_b;j).$$
--   For every pair of natural numbers $m,u$ satisfying
--   $$m\le\begin{cases}2q+3&q_a=q,\\0&q_a\ne q,\end{cases}\quad u\le2q+1,\quad
--   \binom{u+m}2\le qu+(q+1)m,\quad u\le K_q(m,u),\quad (u>0\Rightarrow g_b\ne t_a),$$
--   require the explicit positive-case cost $C_q(m,u;a,b,s,j)\le z$. Here $K_q$ is the candidate-cap function. At every input with $H_{t_a,g_a,q_a}(x)=0$,
--   $$|U_1(H_{t_b,g_b,q},x)|\le z.$$
--   This transfers a finite list of combinatorial case bounds to the output family.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferPositiveStage, SHA256 5a6e7d79cc65ba5305a832db127151744dcf3d8ece0b0198687873a2ec682283; compact solution lines 8819-8868, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_040

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.ordinary_positive_of_cases :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @ZT.LabelCaps k T label →
    ∀ (F : Fin n → (I → Bool) → Bool),
      @OAI.Paper320.NestedFamily n I F →
        ∀ (ta tb ga gb : Fin n),
          @LE.le.{0} (Fin n) (@instLEFin n) ta tb →
            @LE.le.{0} (Fin n) (@instLEFin n) gb ga →
              @LE.le.{0} (Fin n) (@instLEFin n) ga ta →
                ∀ (qa q : Nat),
                  @LE.le.{0} Nat instLENat q qa →
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
                      @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
                        ∀ (a b s j z : Nat),
                          @LE.le.{0} Nat instLENat j s →
                            @ZT.PBound I inst n F gb ta tb a →
                              @ZT.ABound I inst n F gb tb b →
                                @ZT.BBound I inst n F gb ga s →
                                  @ZT.BBound I inst n F gb tb j →
                                    (∀ (m u : Nat),
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
                                                ((@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u
                                                      m).choose
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q u)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    m)) →
                                              @LE.le.{0} Nat instLENat u (ZT.candidateTotalCap q m u) →
                                                (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u →
                                                    @Ne.{1} (Fin n) gb ta) →
                                                  @LE.le.{0} Nat instLENat (ZT.positiveCaseCost q m u a b s j) z) →
                                      ∀
                                        (x :
                                          Prod.{0, 0}
                                              (Prod.{0, 0} (Fin k)
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              I →
                                            Bool),
                                        @Eq.{1} Bool
                                            (@Sensitivity2075.tolerantFamily n k
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F
                                              ta ga qa x)
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
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T
                                                  label F tb gb q)
                                                Bool.true x))
                                            z := by sorry

-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound
-- name    : Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:43:04.338478+00:00
-- url     : https://prove2.me/theorems/2665b5c4-5e98-4853-86a4-bc70145bbd46
-- title:
--   Total candidate cap for positive tolerance
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Assume binary labels satisfy the recorded labeling caps, $g\le t$, and $1\le q\le8$. At any input $x$, let $C(x)$ be the tolerant target set, $G(x)$ the tolerant guard set, and $P(x)$ the positive target set. The explicit candidate-cap function $K_q$ satisfies
--   $$|C(x)|\le K_q(|G(x)|,|P(x)|).$$
--   The finite tournament, nested Boolean family, and input are arbitrary. The function $K_q$ is the finite cap defined in the positive-cap interface; this theorem converts the exclusion conditions into a uniform candidate count.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferPositiveCaps, SHA256 2c8ec868e5f366da81fde081552a9cff6ed3903651a0815c70ec9936b35774cf; compact solution lines 7071-7163, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_030

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound :
∀ {n k : Nat} {I : Type} [Fintype.{0} I] (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @ZT.LabelCaps k T label →
    ∀ (F : Fin n → (I → Bool) → Bool),
      @OAI.Paper320.NestedFamily n I F →
        ∀ (t g : Fin n),
          @LE.le.{0} (Fin n) (@instLEFin n) g t →
            ∀ (q : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
                @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
                  ∀
                    (x :
                      Prod.{0, 0}
                          (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I →
                        Bool),
                    @LE.le.{0} Nat instLENat
                      (@Finset.card.{0} (Fin k)
                        (@Sensitivity2075.tolerantTargets n k
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x))
                      (ZT.candidateTotalCap q
                        (@Finset.card.{0} (Fin k)
                          (@Sensitivity2075.tolerantGuards n k
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x))
                        (@Finset.card.{0} (Fin k)
                          (@SensitivityQ.positiveTargets n k
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
                            (@of_decide_eq_true
                              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@id.{0}
                                (@Eq.{1} Bool
                                  (@Decidable.decide
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  Bool.true)
                                (@Eq.refl.{1} Bool Bool.true)))))) := by sorry

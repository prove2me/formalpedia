-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_rawStep
-- name    : Paley11987Verified.CompactFiniteProfile11987.actual_rawStep
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:06:17.312747+00:00
-- url     : https://prove2.me/theorems/759c4e54-0dce-4b48-b12e-1517daba61c7
-- title:
--   All five raw bounds for an actual Boolean stage
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Suppose $T$ has outdegree $5993$ at every vertex and its binary labeling satisfies the labeling caps. Let $F$ have $20$ levels, nestedness, and scaled profile bounds $(v,c)$. For every valid recipe $r$ satisfying the recorded guard-cost order, the actual stage output $F'$ has all five raw bounds:
--   $$\operatorname{RawStepBounds}(\operatorname{stage}(T,\ell,F,r);v,r,c).$$
--   Concretely, its A, B, M, P, and D conditional bounds are at most $c$ times the corresponding raw coefficient functions, on the admissible index ranges defined in the profile interface. This is the semantic transfer theorem that makes the numerical transition certificates applicable to actual Boolean functions.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferRawStep, SHA256 384ebbc862eb07a950527c55aba9621d88da526bed1b6cbcc29cc50bdbacaf91; compact solution lines 10190-10213, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_042

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile11987.actual_rawStep :
∀ {I : Type} [inst : Fintype.{0} I] {k : Nat} (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @ZT.LabelCaps k T label →
    (∀ (v : Fin k),
        @Eq.{1} Nat
          (@Finset.card.{0} (Fin k)
            (@Finset.filter.{0} (Fin k) (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) v)
              (fun a => Classical.propDecidable (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) v a))
              (@Finset.univ.{0} (Fin k) (Fin.fintype k))))
          (@OfNat.ofNat.{0} Nat (nat_lit 5993) (instOfNatNat (nat_lit 5993)))) →
      ∀ (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → (I → Bool) → Bool),
        @OAI.Paper320.NestedFamily (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F →
          ∀ (v : ZP.Profile) (c : Nat),
            @ZP.ScaledBounds I inst F v c →
              ∀ (r : ZP.Recipe) (hr : ZP.RecipeValid r),
                ZP.GuardCostOrder v r →
                  @ZP.RawStepBounds
                    (Prod.{0, 0}
                      (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
                    (@instFintypeProd.{0, 0}
                      (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I
                      (@instFintypeProd.{0, 0} (Fin k)
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (Fin.fintype k)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      inst)
                    (@ZP.stageFamily I k T label F r hr) v r c := by sorry

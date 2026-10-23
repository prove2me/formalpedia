-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_row_boundary_weighted
-- name    : Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:40:56.326233+00:00
-- url     : https://prove2.me/theorems/056a4834-97a7-4c7c-9d69-d6794588eb79
-- title:
--   A weighted bound for a true row boundary
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Fix a row $v$ at an input $x$ where that row is true. For each label $c$, suppose the child target can be flipped to false at at most $W_c$ coordinates. For each critical guard $w$, suppose its child guard can be flipped to true at at most $V_w$ coordinates. Then
--   $$|U_0(\operatorname{row}_{v,t,g,q},x)|\le\sum_c W_c+\sum_{w\in\operatorname{CriticalGuards}(x,v)}V_w.$$
--   The tournament, finite label alphabet, target and guard levels, and natural weights are arbitrary. This allows row-boundary costs to vary between child coordinates.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferBoundary, SHA256 16c2721a857da820911442f0a8261640b0c79d92dc75cbbe754a1402fb2461ce; compact solution lines 4889-4930, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_021

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted :
∀ {n k r : Nat} {I : Type} [inst : Fintype.{0} I] (T : OAI.Paper320.Tournament k) (label : Fin k → Fin k → Fin r)
  (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : Nat) (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I → Bool)
  (v : Fin k),
  @Eq.{1} Bool (@Sensitivity2075.tolerantRow n k r I T label F t g q x v) Bool.true →
    ∀ (W : Fin r → Nat) (V : Fin k → Nat),
      (∀ (c : Fin r),
          @LE.le.{0} Nat instLENat
            (@Finset.card.{0} I (@ZT.flipsTo I inst (F t) Bool.false (@OAI.Paper320.recursiveChild k r I x v c)))
            (W c)) →
        (∀ (w : Fin k),
            @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
                (@ZT.criticalGuards n k r I T label F g q x v) w →
              @LE.le.{0} Nat instLENat
                (@Finset.card.{0} I
                  (@ZT.flipsTo I inst (F g) Bool.true (@OAI.Paper320.recursiveChild k r I x w (label v w))))
                (V w)) →
          @LE.le.{0} Nat instLENat
            (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I)
              (@ZT.flipsTo (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I)
                (@instFintypeProd.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I
                  (@instFintypeProd.{0, 0} (Fin k) (Fin r) (Fin.fintype k) (Fin.fintype r)) inst)
                (fun y => @Sensitivity2075.tolerantRow n k r I T label F t g q y v) Bool.false x))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Finset.sum.{0, 0} (Fin r) Nat Nat.instAddCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r)) fun c =>
                W c)
              (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid (@ZT.criticalGuards n k r I T label F g q x v)
                fun w => V w)) := by sorry

-- Prove2me | Theorems.Thm_Paley11987Verified_Sensitivity2075_tolerant_repair_cases
-- name    : Paley11987Verified.Sensitivity2075.tolerant_repair_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:36:37.309169+00:00
-- url     : https://prove2.me/theorems/4f35464c-ea9a-42a1-952e-a583447a38ee
-- title:
--   Two ways a bit flip can repair a tolerant row
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Consider a tolerant row $i$ with target level $A$, guard level $G$, and tolerance $q$. Suppose flipping coordinate $(j,c,a)$ changes that row from false to true. Write $x_{j,c}$ for the corresponding child input. Then one of the following alternatives holds:
--   $$\begin{aligned}
--   &i\in\mathrm{Targets}(x),\quad j=i,\quad F_A(x_{j,c})=0,\quad F_A(x_{j,c}\oplus\{a\})=1;\\
--   \text{or }\;&i\in\mathrm{Guards}(x),\quad i\to_T j,\quad c=\ell(i,j),\quad
--   F_G(x_{j,c})=1,\quad F_G(x_{j,c}\oplus\{a\})=0.
--   \end{aligned}$$
--   The tournament, label alphabet, finite child coordinate set, and Boolean family are arbitrary. This classifies the target and guard repairs used in the transfer bounds.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferFoundation, SHA256 d873df15ddf34254fda57ae3742d6727e5a14f23f0375f927f7cf1b57b20b6c9; compact solution lines 4313-4366, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_019

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.Sensitivity2075.tolerant_repair_cases :
∀ {n k r : Nat} {I : Type} (T : OAI.Paper320.Tournament k) (label : Fin k → Fin k → Fin r)
  (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : Nat) (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I → Bool)
  (i j : Fin k) (c : Fin r) (a : I),
  @Eq.{1} Bool (@Sensitivity2075.tolerantRow n k r I T label F A G q x i) Bool.false →
    @Eq.{1} Bool
        (@Sensitivity2075.tolerantRow n k r I T label F A G q
          (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I) x
            (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I)
              (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I))
              (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I))
              (@Prod.mk.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I (@Prod.mk.{0, 0} (Fin k) (Fin r) j c) a)))
          i)
        Bool.true →
      Or
        (And
          (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
            (@Sensitivity2075.tolerantTargets n k r I T label F A G q x) i)
          (And (@Eq.{1} (Fin k) j i)
            (And (@Eq.{1} Bool (F A (@OAI.Paper320.recursiveChild k r I x j c)) Bool.false)
              (@Eq.{1} Bool
                (F A
                  (@OAI.Paper320.flip I (@OAI.Paper320.recursiveChild k r I x j c)
                    (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
                Bool.true))))
        (And
          (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
            (@Sensitivity2075.tolerantGuards n k r I T label F A G q x) i)
          (And (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) i j)
            (And (@Eq.{1} (Fin r) c (label i j))
              (And (@Eq.{1} Bool (F G (@OAI.Paper320.recursiveChild k r I x j c)) Bool.true)
                (@Eq.{1} Bool
                  (F G
                    (@OAI.Paper320.flip I (@OAI.Paper320.recursiveChild k r I x j c)
                      (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
                  Bool.false))))) := by sorry

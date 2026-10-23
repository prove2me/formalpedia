-- Prove2me | Theorems.Thm_Paley11987Verified_Sensitivity2075_tolerant_pair_one
-- name    : Paley11987Verified.Sensitivity2075.tolerant_pair_one
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:38:36.939474+00:00
-- url     : https://prove2.me/theorems/2c5ed12c-bc7f-4ef7-a9d7-9d051bcd7650
-- title:
--   Joint sensitivity of two true tolerant families
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Suppose $T$ has $k$ vertices and constant outdegree $o$, and its labels take $r$ values. Let $J(f,g;x)$ count coordinates at which both $f$ and $g$ change when flipped. Let $Z$ and $Y$ bound this count for ordered pairs of levels of $F$ whose current values are both false and both true, respectively. Choose levels $A_i\le A_j$ and $G_j\le G_i$, and an input $x$ where both $H_{A_i,G_i,q}$ and $H_{A_j,G_j,q}$ are true. Then the joint sensitivity functional $J$ from the transfer foundation satisfies
--   $$J(H_{A_i,G_i,q},H_{A_j,G_j,q};x)\le rY(A_i,A_j)+(o\mathbin{\ominus}q)Z(G_j,G_i).$$
--   The claim holds for all natural $q$ and all finite child coordinate sets. It bounds a pair of true output levels using the corresponding child pair bounds.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferFoundation, SHA256 d873df15ddf34254fda57ae3742d6727e5a14f23f0375f927f7cf1b57b20b6c9; compact solution lines 4537-4642, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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

theorem Paley11987Verified.Sensitivity2075.tolerant_pair_one :
∀ {n k r : Nat} {I : Type} [inst : Fintype.{0} I] (T : OAI.Paper320.Tournament k) (label : Fin k → Fin k → Fin r)
  (F : Fin n → (I → Bool) → Bool),
  @OAI.Paper320.NestedFamily n I F →
    ∀ (o q : Nat),
      (∀ (i : Fin k),
          @Eq.{1} Nat
            (@Finset.card.{0} (Fin k)
              (@Finset.filter.{0} (Fin k) (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) i)
                (fun a =>
                  Classical.propDecidable (@Digraph.Adj.{0} (Fin k) (@OAI.Paper320.Tournament.toDigraph k T) i a))
                (@Finset.univ.{0} (Fin k) (Fin.fintype k))))
            o) →
        ∀ (Z Y : Fin n → Fin n → Nat),
          @Sensitivity205.PairBound n I inst F Bool.false Z →
            @Sensitivity205.PairBound n I inst F Bool.true Y →
              ∀ (Ai Aj Gi Gj : Fin n),
                @LE.le.{0} (Fin n) (@instLEFin n) Ai Aj →
                  @LE.le.{0} (Fin n) (@instLEFin n) Gj Gi →
                    ∀ (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I → Bool),
                      @Eq.{1} Bool (@Sensitivity2075.tolerantFamily n k r I T label F Ai Gi q x) Bool.true →
                        @Eq.{1} Bool (@Sensitivity2075.tolerantFamily n k r I T label F Aj Gj q x) Bool.true →
                          @LE.le.{0} Nat instLENat
                            (@OAI.Paper320.jointSensitivityAt (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I)
                              (@instFintypeProd.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I
                                (@instFintypeProd.{0, 0} (Fin k) (Fin r) (Fin.fintype k) (Fin.fintype r)) inst)
                              (@Sensitivity2075.tolerantFamily n k r I T label F Ai Gi q)
                              (@Sensitivity2075.tolerantFamily n k r I T label F Aj Gj q) x)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r (Y Ai Aj))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) o q) (Z Gj Gi))) := by sorry

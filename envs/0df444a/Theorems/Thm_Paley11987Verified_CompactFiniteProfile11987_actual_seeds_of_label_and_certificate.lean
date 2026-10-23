-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate
-- name    : Paley11987Verified.CompactFiniteProfile11987.actual_seeds_of_label_and_certificate
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:21:52.062897+00:00
-- url     : https://prove2.me/theorems/2758165d-6d90-4ada-9785-8391fd0a35a5
-- title:
--   Actual seed functions from a capped labeling and period certificate
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Suppose a tournament on $11987$ vertices has outdegree $5993$, has a binary labeling satisfying all transfer caps, and satisfies the fixed four-stage period certificate. Then for every natural $m$ there is a finite Boolean function $f_m$ with
--   $$16^m\le s(f_m)\le230508375206254\cdot45238253^m,\qquad
--   11987^{4m}\le bs(f_m).$$
--   This extracts ordinary Boolean functions from the certified nested families.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987Seeds, SHA256 8dd134438fe4217dc4a9a3c76f3e6e940247f7d76ed14b89b3b70eaff0e495ab; compact solution lines 11076-11092, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_051
import Definitions.Def_Paley11987Support_054

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile11987.actual_seeds_of_label_and_certificate :
∀ (T : OAI.Paper320.Tournament (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
  (label :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @ZT.LabelCaps (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) T label →
    (∀ (v : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987)))),
        @Eq.{1} Nat
          (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
            (@Finset.filter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
              (@Digraph.Adj.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                (@OAI.Paper320.Tournament.toDigraph
                  (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) T)
                v)
              (fun a =>
                Classical.propDecidable
                  (@Digraph.Adj.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                    (@OAI.Paper320.Tournament.toDigraph
                      (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) T)
                    v a))
              (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987)))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 5993) (instOfNatNat (nat_lit 5993)))) →
      ZP.PeriodCertificate → ZP.ActualSeedStatement := by sorry

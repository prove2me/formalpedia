-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_families_at_every_cycle
-- name    : Paley11987Verified.CompactFiniteProfile11987.families_at_every_cycle
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:18:06.11714+00:00
-- url     : https://prove2.me/theorems/e3b0235d-272e-4882-818c-e43c4a9fdb3d
-- title:
--   Nested families and lower-bound certificates at every cycle
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Fix a tournament on $11987$ vertices with outdegree $5993$, a binary labeling satisfying the transfer caps, and the fixed period certificate. For every natural $m$ there are a finite coordinate type $I$ and a nested $20$-level Boolean family $F$ such that
--   $$\operatorname{ScaledBounds}(F;v_0,45238253^m),$$
--   $$\operatorname{Blocks}(F,11987^{4m})\ne\varnothing,\qquad
--   \operatorname{SensitiveWitness}(F,16^m)\ne\varnothing.$$
--   The latter two objects are the block-sensitivity and sensitivity witness structures of the seed interface. This packages the iterated upper bounds together with the lower-bound witnesses needed to extract actual functions.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987Seeds, SHA256 8dd134438fe4217dc4a9a3c76f3e6e940247f7d76ed14b89b3b70eaff0e495ab; compact solution lines 11054-11074, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile11987.families_at_every_cycle :
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
      ZP.PeriodCertificate →
        ∀ (m : Nat),
          @Exists.{2} Type fun I =>
            @Exists.{1} (Fintype.{0} I) fun inst =>
              @Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → (I → Bool) → Bool)
                fun F =>
                And (@OAI.Paper320.NestedFamily (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F)
                  (And
                    (@ZP.ScaledBounds I inst F ZP.witness
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) ZP.R
                        m))
                    (And
                      (Nonempty.{1}
                        (@CompactFiniteProfileSeeds.Blocks
                          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            m)))
                      (Nonempty.{1}
                        (@CompactFiniteProfileSeeds.SensitiveWitness
                          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) m))))) := by sorry

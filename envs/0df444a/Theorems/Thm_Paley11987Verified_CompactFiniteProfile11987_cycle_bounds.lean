-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_cycle_bounds
-- name    : Paley11987Verified.CompactFiniteProfile11987.cycle_bounds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:13:33.638508+00:00
-- url     : https://prove2.me/theorems/10d8995f-4c25-4494-8fac-4242750e2e10
-- title:
--   One complete cycle multiplies the profile scale by 45238253
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament on $11987$ vertices with outdegree $5993$ and a binary labeling satisfying the transfer caps. Assume the fixed four-stage period certificate. If a nested $20$-level Boolean family $F$ has the witness profile $v_0$ at natural scale $c$, then
--   $$\operatorname{ScaledBounds}(\operatorname{cycle}(T,\ell,F);v_0,c\cdot45238253).$$
--   The cycle consists of the four recorded recipes. This is the profile invariant used to iterate the construction.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987SeedCycle, SHA256 d0305e4ae9902217ed6df6e96798ee654e5b25ebb83fd749bbb8eb26b71dad32; compact solution lines 10680-10697, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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

theorem Paley11987Verified.CompactFiniteProfile11987.cycle_bounds :
∀ {I : Type} [inst : Fintype.{0} I]
  (T : OAI.Paper320.Tournament (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
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
        ∀ (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → (I → Bool) → Bool),
          @OAI.Paper320.NestedFamily (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F →
            ∀ (c : Nat),
              @ZP.ScaledBounds I inst F ZP.witness c →
                @ZP.ScaledBounds (ZP.CycleCoord I)
                  (@instFintypeProd.{0, 0}
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (ZP.LevelCoord (ZP.LevelCoord (ZP.LevelCoord I)))
                    (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@instFintypeProd.{0, 0}
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (ZP.LevelCoord (ZP.LevelCoord I))
                      (@instFintypeProd.{0, 0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@instFintypeProd.{0, 0}
                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (ZP.LevelCoord I)
                        (@instFintypeProd.{0, 0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@instFintypeProd.{0, 0}
                          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          I
                          (@instFintypeProd.{0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))))
                            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          inst))))
                  (@ZP.cycleFamily I T label F) ZP.witness
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c ZP.R) := by sorry

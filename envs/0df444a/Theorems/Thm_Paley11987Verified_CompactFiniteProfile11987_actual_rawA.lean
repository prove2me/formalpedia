-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_rawA
-- name    : Paley11987Verified.CompactFiniteProfile11987.actual_rawA
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:00:43.095841+00:00
-- url     : https://prove2.me/theorems/da53a501-7b5a-4dac-b124-f621bf3598e5
-- title:
--   The raw A-profile bound for an actual transfer stage
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $T$ be a tournament, $\ell$ its labels, and $F=(F_i)$ a nested family of Boolean functions on a finite coordinate set. Write $H_{t,g,q}$ for the tolerant family obtained from target level $t$, guard level $g$, and tolerance $q$. The symbols $\mathcal A,\mathcal B,\mathcal M,\mathcal P,\mathcal D$ denote the five conditional bounds on the sets $U_b$ defined in the accompanying profile interface. All indices and cost parameters are natural numbers; subtraction between natural numbers is truncated at zero.
--
--   Let $F$ have $20$ levels and scaled profile bounds $(v,c)$. Assume the binary labeling satisfies the labeling caps, and let $r$ be a valid stage recipe. For $0\le i\le j<20$, write $t_i,g_i$ for its target and guard levels. If
--   $$B_v(g_j,t_j)\le B_v(g_j,g_i),$$
--   then the actual output family $F'=\operatorname{stage}(T,\ell,F,r)$ satisfies
--   $$\mathcal A(F';i,j;\ c\,\operatorname{rawA}(v,r;i,j)).$$
--   Here $v$ is a natural-valued profile, $c$ a natural scale, and $B_v$ its B coefficient. This connects the numerical raw-A formula with the actual Boolean operation.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferRawA, SHA256 d24efd214502b6e5c82d645d86d72cdfbe5635bef07cf3c9c8dd9dbe10114553; compact solution lines 9235-9298, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_037

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile11987.actual_rawA :
∀ {I : Type} [inst : Fintype.{0} I] {k : Nat} (T : OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @ZT.LabelCaps k T label →
    ∀ (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → (I → Bool) → Bool),
      @OAI.Paper320.NestedFamily (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) I F →
        ∀ (v : ZP.Profile) (c : Nat),
          @ZP.ScaledBounds I inst F v c →
            ∀ (r : ZP.Recipe) (hr : ZP.RecipeValid r)
              (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))),
              @LE.le.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                  (@instLEFin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) i j →
                @LE.le.{0} Nat instLENat
                    (ZP.B v
                      (@Option.getD.{0} ZP.RecipeEntry
                          (@GetElem?.getElem?.{0, 0, 0} ZP.Recipe Nat ZP.RecipeEntry
                            (fun xs i => @LT.lt.{0} Nat instLTNat i (@Array.size.{0} ZP.RecipeEntry xs))
                            (@Array.instGetElem?NatLtSize.{0} ZP.RecipeEntry) r
                            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) j))
                          (@Inhabited.default.{1} ZP.RecipeEntry ZP.instInhabitedRecipeEntry)).guard
                      (@Option.getD.{0} ZP.RecipeEntry
                          (@GetElem?.getElem?.{0, 0, 0} ZP.Recipe Nat ZP.RecipeEntry
                            (fun xs i => @LT.lt.{0} Nat instLTNat i (@Array.size.{0} ZP.RecipeEntry xs))
                            (@Array.instGetElem?NatLtSize.{0} ZP.RecipeEntry) r
                            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) j))
                          (@Inhabited.default.{1} ZP.RecipeEntry ZP.instInhabitedRecipeEntry)).target)
                    (ZP.B v
                      (@Option.getD.{0} ZP.RecipeEntry
                          (@GetElem?.getElem?.{0, 0, 0} ZP.Recipe Nat ZP.RecipeEntry
                            (fun xs i => @LT.lt.{0} Nat instLTNat i (@Array.size.{0} ZP.RecipeEntry xs))
                            (@Array.instGetElem?NatLtSize.{0} ZP.RecipeEntry) r
                            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) j))
                          (@Inhabited.default.{1} ZP.RecipeEntry ZP.instInhabitedRecipeEntry)).guard
                      (@Option.getD.{0} ZP.RecipeEntry
                          (@GetElem?.getElem?.{0, 0, 0} ZP.Recipe Nat ZP.RecipeEntry
                            (fun xs i => @LT.lt.{0} Nat instLTNat i (@Array.size.{0} ZP.RecipeEntry xs))
                            (@Array.instGetElem?NatLtSize.{0} ZP.RecipeEntry) r
                            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) i))
                          (@Inhabited.default.{1} ZP.RecipeEntry ZP.instInhabitedRecipeEntry)).guard) →
                  @ZT.ABound
                    (Prod.{0, 0}
                      (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
                    (@instFintypeProd.{0, 0}
                      (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I
                      (@instFintypeProd.{0, 0} (Fin k)
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (Fin.fintype k)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      inst)
                    (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) (@ZP.stageFamily I k T label F r hr)
                    i j
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
                      (ZP.rawA v r (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) i)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) j))) := by sorry

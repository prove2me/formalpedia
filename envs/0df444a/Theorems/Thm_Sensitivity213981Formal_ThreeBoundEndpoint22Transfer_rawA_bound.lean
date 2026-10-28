-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Transfer_rawA_bound
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.rawA_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:41.495601+00:00
-- url     : https://prove2.me/theorems/0c0b7ccb-3246-43ea-b6f0-6905a4cbd2c3
-- title:
--   raw A bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl(\operatorname{Endpoint22Transfer.TripleGeometry}\Longrightarrow \forall \mathit{records}:\operatorname{List}(\operatorname{List}(\mathbb N)),\quad \bigl(\forall \mathit{xs}:\operatorname{List}(\mathbb N),\quad \bigl(\mathit{xs}\in \operatorname{Q3.records}\Longrightarrow \mathit{xs}\in \mathit{records}\bigr)\Longrightarrow \forall p:\{0,\ldots,4-1\},\quad \forall F:\left(\{0,\ldots,22-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(22\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \bigl(\operatorname{Numeric.Ordered}\bigl(v\bigr)\Longrightarrow \forall i:\{0,\ldots,22-1\},\quad \forall j:\{0,\ldots,22-1\},\quad \bigl(\bigl(i \le j\bigr)\Longrightarrow \operatorname{Profiles.ABound}\bigl(\operatorname{Witness.parent}\bigl(\operatorname{MinMaxRecipe.stage}\bigl(\operatorname{Sensitivity5591Endpoint22.recipe}\bigl(\operatorname{Labeling5591.Adj}, \operatorname{Labeling5591.irreflexive}, \operatorname{Labeling5591.label}\bigl(\mathit{htriple}\bigr), p\bigr), F\bigr), F\bigr), i, j, \operatorname{Expr.eval}\bigl(v, \operatorname{RankNumeric.rawAExpr}\bigl(22, \operatorname{Ordinary5591.numericCaps}, 14, \mathit{records}, \operatorname{Endpoint22.recipe}\bigl(p, i\bigr), \operatorname{Endpoint22.recipe}\bigl(p, j\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding raw A bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Transfer.lean, lines 66–89.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
import Definitions.Def_Sensitivity213981Formal_Endpoint22Transfer
import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Label5591Joint
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Selected5591
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.rawA_bound :
∀ {I : Type} [inst : Fintype.{0} I] (htriple : Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.TripleGeometry)
  (records : List.{0} (List.{0} Nat))
  (hrecords :
    ∀ (xs : List.{0} Nat),
      @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          Sensitivity213981Formal.ThreeBoundQ3.records xs →
        @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          records xs)
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
      F)
  (v :
    Sensitivity213981Formal.ThreeBoundFullProfile.Profile
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hv :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      I inst F v)
  (hordered :
    @Sensitivity213981Formal.ThreeBoundNumeric.Ordered (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      v)
  (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hij :
    @LE.le.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
      (@instLEFin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) i j),
  @Sensitivity213981Formal.ThreeBoundProfiles.ABound
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
    (Prod.{0, 0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I)
    (@instFintypeProd.{0, 0}
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I
      (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool.fintype)
      inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (@Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe.stage
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
        (Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe
          Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.Adj
          Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.irreflexive
          (Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.label htriple) p)
        F)
      F)
    i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) v
      (Sensitivity213981Formal.ThreeBoundRankNumeric.rawAExpr
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) records
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))) := by sorry

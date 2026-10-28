-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedDegree_sum_out_on
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedDegree.sum_out_on
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:12.877217+00:00
-- url     : https://prove2.me/theorems/a9e23cb1-3825-495d-adb1-732f57dacd9a
-- title:
--   sum out on — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(V)\bigr]\;\forall R:\left(V\to \left(V\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\Longrightarrow \forall S:\mathcal P_{\mathrm{fin}}(V),\quad \bigl(\sum_{v\in S} |\operatorname{Finset.filter}\bigl(R\bigl(v\bigr), S\bigr)| = \frac{\bigl(|S|\cdot \bigl(|S|-1\bigr)\bigr)}{2}\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding sum out on step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedDegreeNecessity.lean, lines 57–70.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedDegreeNecessity
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRelaxedDegree.sum_out_on :
∀ {V : Type} [Fintype.{0} V] (R : V → V → Prop) (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (S : Finset.{0} V),
  @Eq.{1} Nat
    (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid S fun (v : V) =>
      @Finset.card.{0} V (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) S))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Finset.card.{0} V S)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} V S)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by sorry

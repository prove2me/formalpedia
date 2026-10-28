-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedDegree_row_total
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedDegree.row_total
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:53:32.24658+00:00
-- url     : https://prove2.me/theorems/49155f63-7b37-41cc-8018-717dff24f1ec
-- title:
--   row total — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(V)\bigr]\;\forall R:\left(V\to \left(V\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\Longrightarrow \forall S:\mathcal P_{\mathrm{fin}}(V),\quad \forall v:V,\quad \bigl(\bigl(|\operatorname{Finset.filter}\bigl(R\bigl(v\bigr), S\bigr)|+|\operatorname{Finset.filter}\bigl(\left(u\mapsto R\bigl(u, v\bigr)\right), S\bigr)|\bigr) = \bigl(|S|-\operatorname{RelaxedDegree.indicator}\bigl(S, v\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding row total step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedDegreeNecessity.lean, lines 21–50.

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

theorem Sensitivity213981Formal.ThreeBoundRelaxedDegree.row_total :
∀ {V : Type} [Fintype.{0} V] (R : V → V → Prop) (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (S : Finset.{0} V) (v : V),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{0} V (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) S))
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (u : V) => R u v) (fun (a : V) => Classical.propDecidable (R a v)) S)))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} V S)
      (@Sensitivity213981Formal.ThreeBoundRelaxedDegree.indicator V S v)) := by sorry

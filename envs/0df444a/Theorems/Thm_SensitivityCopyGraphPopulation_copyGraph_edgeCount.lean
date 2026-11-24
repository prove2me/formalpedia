-- Prove2me | Theorems.Thm_SensitivityCopyGraphPopulation_copyGraph_edgeCount
-- name    : SensitivityCopyGraphPopulation.copyGraph_edgeCount
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:14.711804+00:00
-- url     : https://prove2.me/theorems/b715f862-0cb1-4564-ba59-557a790958a7
-- title:
--   Edge count of disjoint induced graph copies
-- statement:
--   Let $G$ be a simple graph on a set $V$, let $C$ be finite, and let $S_c\subseteq V$ be a finite vertex set for each $c\in C$. Form a graph whose vertices are tagged pairs $(c,v)$ with $v\in S_c$, with edges only between vertices carrying the same tag and adjacent in $G$. Then
--
--   $$e\!\left(\coprod_{c\in C}G[S_c]\right)=\sum_{c\in C}e(G[S_c]).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/CopyGraphPopulation.lean lines 93–111; SHA256 85a3bfd1a112a309991510267a172686b2463acf7d058d438334fcdf13dbbb51; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityCopyGraphPopulation
end SensitivityCopyGraphPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation


/-! Disjoint copies of induced conflict graphs, with exact integral edge bounds. -/
open SensitivityCopyGraphPopulation
open scoped Classical BigOperators
open SensitivityGraphPopulation SensitivityActiveSocketPopulation
set_option autoImplicit false
variable {C V : Type} [Fintype C]

theorem SensitivityCopyGraphPopulation.copyGraph_edgeCount (G : SimpleGraph V) (sets : C → Finset V) :
    edgeCount (copyGraph G sets) =
      ∑ c, edgeCount (G.induce (↑(sets c) : Set V)) := by sorry

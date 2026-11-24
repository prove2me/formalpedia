-- Prove2me | Theorems.Thm_SensitivityCopyGraphPopulation_copyGraph_independence_bound
-- name    : SensitivityCopyGraphPopulation.copyGraph_independence_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:14.114736+00:00
-- url     : https://prove2.me/theorems/b3f74e71-77e9-4fb9-908b-8dd002f31625
-- title:
--   Independent sets in disjoint induced graph copies
-- statement:
--   Let $G$ be a simple graph, and let $(S_c)_{c\in C}$ be a finite family of finite vertex sets. Suppose every independent subset of $S_c$ has size at most $\alpha_c$. In the disjoint graph with a separate tagged copy of $G[S_c]$ for each $c$, every independent set $A$ satisfies
--
--   $$|A|\le\sum_{c\in C}\alpha_c.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/CopyGraphPopulation.lean lines 25–65; SHA256 85a3bfd1a112a309991510267a172686b2463acf7d058d438334fcdf13dbbb51; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
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

theorem SensitivityCopyGraphPopulation.copyGraph_independence_bound (G : SimpleGraph V) (sets : C → Finset V)
    (alpha : C → ℕ)
    (hcap : ∀ c, ∀ s ⊆ sets c, G.IsIndepSet s → s.card ≤ alpha c) :
    ∀ vertices : Finset (CopyVertex sets), (copyGraph G sets).IsIndepSet vertices →
      vertices.card ≤ ∑ c, alpha c := by sorry

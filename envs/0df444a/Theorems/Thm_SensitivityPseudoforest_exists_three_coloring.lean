-- Prove2me | Theorems.Thm_SensitivityPseudoforest_exists_three_coloring
-- name    : SensitivityPseudoforest.exists_three_coloring
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:18.943677+00:00
-- url     : https://prove2.me/theorems/924aee6e-cc0e-4919-8cba-d1fc98a85d27
-- title:
--   Three-coloring a finite relation of maximum neighbor degree two
-- statement:
--   Let $R$ be an irreflexive relation on $V$, and let $S\subseteq V$ be finite. Suppose that every $v\in S$ has at most two neighbors in $S$, counting a vertex $w$ as a neighbor when $R(v,w)$ or $R(w,v)$. There is a map $c:V\to\{0,1,2\}$ such that
--
--   $$v,w\in S,\ R(v,w)\quad\Longrightarrow\quad c(v)\ne c(w).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PseudoforestCover.lean lines 79–123; SHA256 e5f8acc9d97d8c67914f3708144ec7d81a98e150401cacf5ad609edb8b64f010; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Tauto

namespace SensitivityPseudoforest
end SensitivityPseudoforest


/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/
open SensitivityPseudoforest
open scoped Classical BigOperators
set_option autoImplicit false
variable {V : Type}

theorem SensitivityPseudoforest.exists_three_coloring (R : V → V → Prop) (hirr : ∀ v, ¬ R v v) :
    ∀ s : Finset V, (∀ v ∈ s, (neighbors R s v).card ≤ 2) →
      ∃ color : V → Fin 3, ∀ v ∈ s, ∀ w ∈ s, R v w → color v ≠ color w := by sorry

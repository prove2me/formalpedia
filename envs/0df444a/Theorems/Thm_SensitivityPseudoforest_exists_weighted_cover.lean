-- Prove2me | Theorems.Thm_SensitivityPseudoforest_exists_weighted_cover
-- name    : SensitivityPseudoforest.exists_weighted_cover
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:21.526061+00:00
-- url     : https://prove2.me/theorems/5e831761-7ead-43f0-8ee2-8e364d4c5908
-- title:
--   Three independent palettes with doubled sinks
-- statement:
--   Let $R$ be an irreflexive relation and let $S$ be finite. Suppose every vertex of $S$ has at most one outgoing neighbor in $S$. There exists an assignment $P(v)\subseteq\{0,1,2\}$ such that, for $v\in S$,
--
--   $$|P(v)|=\begin{cases}2,&v\text{ has no outgoing neighbor in }S,\\1,&\text{otherwise},\end{cases}$$
--
--   and $P(v)\cap P(w)=\varnothing$ whenever $v,w\in S$ and $R(v,w)$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PseudoforestCover.lean lines 162–223; SHA256 e5f8acc9d97d8c67914f3708144ec7d81a98e150401cacf5ad609edb8b64f010; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityPseudoforest.exists_weighted_cover (R : V → V → Prop) (hirr : ∀ v, ¬ R v v) :
    ∀ s : Finset V, (∀ v ∈ s, (outgoing R s v).card ≤ 1) → Nonempty (WeightedCover R s) := by sorry

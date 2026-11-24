-- Prove2me | Theorems.Thm_SensitivityPseudoforest_population_sinks_bound
-- name    : SensitivityPseudoforest.population_sinks_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:19:17.965309+00:00
-- url     : https://prove2.me/theorems/ba11e755-6b81-42d4-8d07-fdfea1c53bed
-- title:
--   Population plus sinks in an outdegree-one relation
-- statement:
--   Let $R$ be an irreflexive relation on a finite set $S$. Suppose each vertex has at most one outgoing neighbor in $S$, and every subset containing no directed edge has cardinality at most $\alpha$. If $Z$ is the set of sinks in $S$, then
--
--   $$|S|+|Z|\le3\alpha.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PseudoforestCover.lean lines 225–260; SHA256 e5f8acc9d97d8c67914f3708144ec7d81a98e150401cacf5ad609edb8b64f010; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityPseudoforest.population_sinks_bound (R : V → V → Prop) (hirr : ∀ v, ¬ R v v)
    (s : Finset V) (alpha : ℕ)
    (hout : ∀ v ∈ s, (outgoing R s v).card ≤ 1)
    (hind : ∀ t ⊆ s, (∀ v ∈ t, ∀ w ∈ t, ¬ R v w) → t.card ≤ alpha) :
    s.card + (s.filter (IsSink R s)).card ≤ 3 * alpha := by sorry

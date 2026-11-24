-- Prove2me | Theorems.Thm_SensitivityMarkerPowerAlpha_cap_from_macro_markers
-- name    : SensitivityMarkerPowerAlpha.cap_from_macro_markers
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:27.939036+00:00
-- url     : https://prove2.me/theorems/68ce2835-3d06-4459-a4c0-79ffab47f858
-- title:
--   Domination cap from the number of distinct marker macros
-- statement:
--   Let $H$ be a nonempty finite marker set, let $\gamma:H\to M$ assign each marker to a macro, and let $C$ be a finite candidate set dominated by every marker macro in $\gamma(H)$. Suppose simultaneous domination by one, two distinct, or three distinct macros bounds $|C|$ by $b_1,b_2,b_3$, respectively. Then
--
--   $$|C|\le
--   \begin{cases}
--   b_1,&|\gamma(H)|=1,\\
--   b_2,&|\gamma(H)|=2,\\
--   b_3,&|\gamma(H)|\ge3.
--   \end{cases}$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerPowerAlpha.lean lines 85–106; SHA256 cf85bfd72311724e56b23121de54fc4f0aec3a257ee6f57b5ffba4b57fae9ca5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCaps
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityClusterPartitionBound
end SensitivityClusterPartitionBound
namespace SensitivityMarkerClusterCaps
end SensitivityMarkerClusterCaps
namespace SensitivityMarkerClusterCounts
end SensitivityMarkerClusterCounts
namespace SensitivityMarkerPowerAlpha
end SensitivityMarkerPowerAlpha


/-! Exact finite partition formulas for the source's summed marker capacities. -/
open SensitivityMarkerPowerAlpha
open scoped Classical BigOperators
open SensitivityMarkerClusterCounts SensitivityMarkerClusterCaps SensitivityClusterPartitionBound
set_option autoImplicit false
variable {V M W : Type} [DecidableEq V] [DecidableEq M]

theorem SensitivityMarkerPowerAlpha.cap_from_macro_markers (selected : Finset V) (group : V → M)
    (hselected : selected.Nonempty) (candidates : Finset W) (dominates : M → W → Prop)
    (b1 b2 b3 : ℕ)
    (hdom : ∀ marker ∈ selected, ∀ v ∈ candidates, dominates (group marker) v)
    (hone : ∀ p, (∀ v ∈ candidates, dominates p v) → candidates.card ≤ b1)
    (htwo : ∀ p q, p ≠ q → (∀ v ∈ candidates, dominates p v ∧ dominates q v) → candidates.card ≤ b2)
    (hthree : ∀ p q r, p ≠ q → p ≠ r → q ≠ r →
      (∀ v ∈ candidates, dominates p v ∧ dominates q v ∧ dominates r v) → candidates.card ≤ b3) :
    candidates.card ≤ markerCap b1 b2 b3 group selected := by sorry

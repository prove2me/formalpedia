-- Prove2me | Theorems.Thm_SensitivityPairedPopulation_Admissible_reduced
-- name    : SensitivityPairedPopulation.Admissible.reduced
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:26.6091+00:00
-- url     : https://prove2.me/theorems/f0e59bef-0710-4213-9ca6-430d60c6d5b4
-- title:
--   A graded admissible population satisfies the reduced two-count constraints
-- statement:
--   Let $D$ be a graded geometry and $n$ a four-tier population admissible for $D$. At its tolerance tier $q$, let $a$ be the population strictly below $q$ and $b$ the population at or below $q$. Then $(a,b)$ satisfies the ReducedAdmissible predicate for $D$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PairedReducedPopulation.lean lines 112–163; SHA256 bb4f564266cfbd1a4b08b7a05c204f629f7b26199b735a5395226dcf43cb89d7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedReducedPopulation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityPairedPopulation
end SensitivityPairedPopulation


/-! The literal paired objectives have a common price on all tiers below the
last. Their finite population bound therefore needs two cumulative counts. -/
open SensitivityPairedPopulation

theorem SensitivityPairedPopulation.Admissible.reduced {data : GradedGeometry} {n : Population}
    (h : Admissible data n) :
    ReducedAdmissible data (previousCount n data.tolerance) (prefixCount n data.tolerance) := by sorry

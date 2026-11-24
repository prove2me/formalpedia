-- Prove2me | Theorems.Thm_SensitivityPairedPopulation_weightedCount_reduced
-- name    : SensitivityPairedPopulation.weightedCount_reduced
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:24.714825+00:00
-- url     : https://prove2.me/theorems/25ea1319-804c-4cb8-982f-a148ea33db57
-- title:
--   A common lower-tier price reduces the weighted population to two counts
-- statement:
--   Let $p_0,p_1,p_2,p_3$ be nonnegative integer prices, let $n$ be a four-tier population, and let $q$ be its cutoff tier. Suppose the CommonLowerPrice predicate holds: all tiers below $q$ have the price of the preceding tier. Writing $a$ for the population strictly below $q$ and $b$ for the population at or below $q$, the weighted count through $q$ is
--
--   $$a\,p_{\mathrm{prev}(q)}+(b-a)p_q.$$
--
--   The convention for the preceding tier at $q=0$ is the one in the reduced-population definition.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PairedReducedPopulation.lean lines 172–189; SHA256 bb4f564266cfbd1a4b08b7a05c204f629f7b26199b735a5395226dcf43cb89d7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityPairedPopulation.weightedCount_reduced (prices : Fin 4 → ℕ) (n : Population) (q : Fin 4)
    (h : CommonLowerPrice prices q) :
    weightedCount prices n q = previousCount n q * prices (previousTier q) +
      (prefixCount n q - previousCount n q) * prices q := by sorry

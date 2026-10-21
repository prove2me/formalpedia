-- Prove2me | Theorems.Thm_SolarTariff_Fair_welfare_decomposition
-- name    : SolarTariff.Fair.welfare_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:30.653352+00:00
-- url     : https://prove2.me/theorems/eae2f7c9-c269-4b73-852e-6f363784f899
-- title:
--   §4, p. 12 — decomposition of financial welfare
-- statement:
--   For a tariff, target adopting set $A$, and solar price $p_s$, suppose the utility receives its specified profit change $\Delta_U$ and the solar company earns $\Delta_S$ at volume $\Delta_E^A$. Then the household weighted sum of customers' decreases in cash outflow is their aggregate financial gain:
--
--   $$\sum_i h_i\bigl[-\Delta\mathrm{outflow}_i\bigr]=\Delta_C=\Delta_{WF}-\Delta_S-\Delta_U.$$
--
--   This is the paper's financial welfare decomposition. It links the customer equity objective to the system's financial flows.
--
--   **Formalization Note** The sum uses household counts $h_i$, required by the paper's proof on p. S.3; the displayed definition of $\Delta_C$ on p. 12 omits those weights.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. 12 (PDF 12), §4, paragraph after (6); p. S.3 (PDF 35), proof of Proposition 5

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem welfare_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (B : Bills ι) (A : Finset ι) (ps : ℝ)
    (hU : utilityChange M B A = M.dU)
    (hS : (ps - M.cs (DeltaE M A)) * DeltaE M A = M.dS) :
    (∑ i, M.h i * (-outflowChange M B A ps i)) = dC M A := by sorry

end SolarTariff.Fair

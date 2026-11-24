-- Prove2me | Theorems.Thm_SensitivityUnaryWarmGlobalNumeric_phase0_warm_a_6_11
-- name    : SensitivityUnaryWarmGlobalNumeric.phase0_warm_a_6_11
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:04:36.256792+00:00
-- url     : https://prove2.me/theorems/aef8e7e3-d24c-43d3-9f27-4336ceb93b2c
-- title:
--   Unary warm global gain certificate at ranks $(6,11)$
-- statement:
--   Fix ranks $(i,j)=(6,11)$ in the unary Paley recipe, with checkpoint input profile $v$ and first image $w$. Let $(L,T,T^*,E,I,\ell)$ be the stored prices: low-row, target-row, marked-target, external, and internal prices, together with a loss price $\ell(h)$ for each height. These prices satisfy all local constraints at every rejected enumerated warm state, $\ell(h)\le E$ for $0\le h\le12$, and
--
--   $$\max\{2659L,\ 1329L+T,\ 664L+T^*,\ 664L+E,\ 344L+I+E,\ 344L+3I\}\le A_w(6,11).$$
--
--   The local constraints bound low-row fees by $L$, target and marked-target fees by $T$ and $T^*$, individual high-guard charges by $\ell$, and an internal hard-row loss by $I$ whenever that case is possible. The displayed maximum is the common bound for the six global Paley population cases. This certificate supplies the numerical prices for the global unary gain coordinate $A_w(i,j)$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryWarmGlobalChecks/A06_11.lean lines 7–9; SHA256 480585586391eceb2c33da52a936e7b104af40591962039385296d0d2f3e31ed; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryWarmGlobalNumeric
end SensitivityUnaryWarmGlobalNumeric


open SensitivityUnaryWarmGlobalNumeric
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SensitivityUnaryWarmGlobalNumeric.phase0_warm_a_6_11 :
    check SensitivityUnaryGainNumeric.phase0 SensitivityLiteralRay.rayData 6 11 prices_6_11
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 0 6 11) = true := by sorry

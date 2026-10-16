-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_agent2_truthful_half
-- name    : StrategicAlloc.CutChoose.agent2_truthful_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:43.265178+00:00
-- url     : https://prove2.me/theorems/7fa9174d-e7a7-47ce-b1cd-3699256c298a
-- title:
--   §4.1, p. 18, proof of Theorem 4.3 — by bidding truthfully agent 2 gets at least v₂(M)/2
-- statement:
--   Consider two agents with additive non-negative valuations $v_1,v_2$ on the set $M$ of goods and Mod-Cut&Choose. Whatever agent 1 bids, if agent 2 declares her truthful bid $v_2$ she receives a bundle of value at least half of her value for all goods:
--   $$v_2\big(\mathcal M(\mathbf b_1,v_2)_2\big)\ \ge\ \frac{v_2(M)}{2}.$$
--
--   Combined with $2\mu_2\le v_2(M)$, this shows that deviating to the truthful bid would give agent 2 at least her maximin share, which is the agent-2 half of the MMS part of Theorem 4.3.
--
--   **Formalization Note** The profile $(\mathbf b_1,v_2)$ is `Function.update b 1 (v 1)` for an arbitrary profile `b`; only `b 0` (agent 1's bid) matters.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 18, §4.1, proof of Theorem 4.3, fourth paragraph

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Proof of Theorem 4.3 (p. 18), fourth paragraph: whatever agent 1 bids, agent 2's truthful
bid gives her a bundle of value at least `v_2(M)/2`. -/
theorem agent2_truthful_half {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) :
    StrategicAlloc.RRFair.val v 1 Finset.univ / 2 ≤ StrategicAlloc.RRFair.val v 1 (modCutChoose (Function.update b 1 (v 1)) 1) := by sorry

end StrategicAlloc.CutChoose

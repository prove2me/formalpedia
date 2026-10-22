-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_agent2_truthful_dominant
-- name    : StrategicAlloc.CutChoose.agent2_truthful_dominant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:28.839888+00:00
-- url     : https://prove2.me/theorems/cd7809d7-8a98-46a9-97ca-d7eb8edfa9c4
-- title:
--   §4.1, p. 18, proof of Theorem 4.3 — truthful bidding is a dominant strategy for agent 2
-- statement:
--   Consider two agents with additive non-negative valuations $v_1,v_2$ and Mod-Cut&Choose. For every bid profile $\mathbf b=(\mathbf b_1,\mathbf b_2)$ with non-negative bids, replace agent 2's bid by her truthful bid $v_2=(v_2(g_1),\dots,v_2(g_m))$. Then agent 2's truthful bid is a best response to $\mathbf b_1$: for every $\mathbf b'_2\in\mathbb R^m_{\ge 0}$,
--   $$v_2\big(\mathcal M(\mathbf b_1,\mathbf b'_2)_2\big)\ \le\ v_2\big(\mathcal M(\mathbf b_1,v_2)_2\big).$$
--
--   Since agent 1's bid alone determines the cut, agent 2 can only choose between the two bundles, and bidding truthfully picks the one she values more. Truth telling is thus a dominant strategy for agent 2, which settles her part of the equilibrium in Theorem 4.3.
--
--   **Formalization Note** The profile $(\mathbf b_1,v_2)$ is `Function.update b 1 (v 1)`; agent 2 is `1`.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 18, §4.1, proof of Theorem 4.3, third paragraph

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Proof of Theorem 4.3 (p. 18), third paragraph: whatever agent 1 bids, agent 2's truthful bid
`v_2` is a best response in Mod-Cut&Choose (truth telling is a dominant strategy for agent 2). -/
theorem agent2_truthful_dominant {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) (hb : StrategicAlloc.RRFair.IsBidProfile b) :
    StrategicAlloc.RRFair.IsBestResponse modCutChoose v (Function.update b 1 (v 1)) 1 := by sorry

end StrategicAlloc.CutChoose

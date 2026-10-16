-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_corollary_4_2
-- name    : StrategicAlloc.CutChoose.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:42.963029+00:00
-- url     : https://prove2.me/theorems/e42f9958-bba0-43bb-81e4-46d2474c798a
-- title:
--   Corollary 4.2 — agent 1 can force Mod-Cut&Choose to cut a µ₁-partition
-- statement:
--   Consider two agents with additive non-negative valuations $v_1,v_2$ on $m$ goods, and let $\mu_1=\mu_1(2,M)$ be agent 1's maximin share. A pair $(E_1,E_2)$ partitioning $M$ with
--   $$\min\{v_1(E_1),v_1(E_2)\}=\mu_1$$
--   is called a $\mu_1$-partition. Agent 1 has a bid vector $\mathbf b_1\in\mathbb R^m_{\ge 0}$ under which lines 1–5 of Mod-Cut&Choose construct a $\mu_1$-partition.
--
--   Whatever bundle agent 2 then takes, agent 1 is left with a bundle worth at least $\mu_1$ to her; this is how the proof of Theorem 4.3 shows that every equilibrium gives agent 1 her maximin share.
--
--   **Formalization Note** `cut c` is the pair $(E_1,E_2)$ after line 5 when agent 1 bids $c$; values are measured with agent 1's true valuation $v_1$ (agent `0`).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 18, Corollary 4.2 and the paragraph before it

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Corollary 4.2 (p. 18): agent 1 has a non-negative bid vector under which lines 3–5 of
Mod-Cut&Choose construct a `µ_1`-partition, i.e. `min {v_1(E_1), v_1(E_2)} = µ_1`. -/
theorem corollary_4_2 {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ c : Fin m → ℝ, (∀ g, 0 ≤ c g) ∧
      min (StrategicAlloc.RRFair.val v 0 (cut c).1) (StrategicAlloc.RRFair.val v 0 (cut c).2) = mu v 0 := by sorry

end StrategicAlloc.CutChoose

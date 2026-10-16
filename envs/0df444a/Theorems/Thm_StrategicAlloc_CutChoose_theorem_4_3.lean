-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_theorem_4_3
-- name    : StrategicAlloc.CutChoose.theorem_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:40.207172+00:00
-- url     : https://prove2.me/theorems/1f829ec8-014f-4f14-95ee-2b41fb123722
-- title:
--   Theorem 4.3 — Mod-Cut&Choose has a pure Nash equilibrium, and every one is MMS and EFX
-- statement:
--   Let $\mathcal I=(\{1,2\},M,\mathbf v)$ be any instance with two agents whose additive valuations $v_1,v_2$ are non-negative on the $m$ goods of $M$, and let $\mathcal M$ be the Mod-Cut&Choose mechanism (Mechanism 2). Then:
--
--   1. $\mathcal M$ has at least one pure Nash equilibrium: a bid profile $\mathbf b=(\mathbf b_1,\mathbf b_2)\in(\mathbb R^m_{\ge 0})^2$ such that no agent $i$ has a bid $\mathbf b'_i\in\mathbb R^m_{\ge 0}$ with $v_i(\mathcal M(\mathbf b'_i,\mathbf b_{-i}))>v_i(\mathcal M(\mathbf b))$;
--   2. for every pure Nash equilibrium $\mathbf b$, the allocation $\mathcal A=\mathcal M(\mathbf b)$ is MMS and EFX with respect to the true valuations:
--   $$v_i(A_i)\ \ge\ \mu_i\quad (i=1,2),\qquad \mathcal A \text{ is EFX w.r.t. } v_1,v_2.$$
--
--   Here $\mu_i=\mu_i(2,M)$ is agent $i$'s maximin share and EFX is Definition 2.1. Although Mod-Cut&Choose is not truthful, and as an algorithm it does not guarantee more than $5/6$ of the maximin share, its equilibria are exactly as fair as one could ask for two agents.
--
--   **Formalization Note** Agents are `0` (agent 1) and `1` (agent 2). Deviations range over all non-negative bid vectors, and fairness is measured with the true valuations $v$, not with the bids. The mechanism sorts goods by agent 1's bid rather than by $v_1$ as the page's line 2 says (a disclosed correction; see the Mod-Cut&Choose definition).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 18, Theorem 4.3

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Theorem 4.3 (p. 18): for every two-agent instance with additive non-negative valuations,
Mod-Cut&Choose has a pure Nash equilibrium, and every pure Nash equilibrium yields an allocation
that is MMS and EFX with respect to the true valuations `v_1, v_2`. -/
theorem theorem_4_3 {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    (∃ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b) ∧
      ∀ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b →
        IsApproxMMS 1 v (modCutChoose b) ∧ IsEFX v (modCutChoose b) := by sorry

end StrategicAlloc.CutChoose

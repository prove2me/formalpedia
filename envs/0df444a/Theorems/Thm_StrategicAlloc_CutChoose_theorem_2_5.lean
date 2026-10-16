-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_theorem_2_5
-- name    : StrategicAlloc.CutChoose.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:39.282504+00:00
-- url     : https://prove2.me/theorems/ce17a3ec-7a86-4b0b-8982-bcb43d6f8c00
-- title:
--   Theorem 2.5 — for two agents every MMS allocation is EFX
-- statement:
--   Let two agents have additive valuations $v_1,v_2$ with non-negative values $v_i(g)\ge 0$ on a set $M$ of $m$ goods, and let $\mathcal A=(A_1,A_2)$ be an allocation, i.e. a partition of $M$. Write $\mu_i=\mu_i(2,M)$ for the maximin share of agent $i$. If $\mathcal A$ is MMS, that is,
--   $$v_i(A_i)\ \ge\ \mu_i\qquad (i=1,2),$$
--   then $\mathcal A$ is EFX: for all $i,j$ with $A_j\neq\emptyset$ and every $g\in A_j$ with $v_i(g)>0$, $v_i(A_i)\ge v_i(A_j\setminus\{g\})$.
--
--   The paper attributes this to Theorem 4.6 of Caragiannis et al. It turns the MMS guarantee of the equilibria of Mod-Cut&Choose into an EFX guarantee in the last step of the proof of Theorem 4.3.
--
--   **Formalization Note** EFX is the paper's Definition 2.1, which removes only goods of positive value; with the stronger variant that also removes zero-valued goods the statement would be false.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 5, Theorem 2.5

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Theorem 2.5 (p. 5): for two agents with additive non-negative valuations, every MMS
allocation is an EFX allocation (EFX as in Definition 2.1: only goods of positive value are
removed). -/
theorem theorem_2_5 {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : StrategicAlloc.RRFair.IsAllocation A) (hmms : IsApproxMMS 1 v A) :
    IsEFX v A := by sorry

end StrategicAlloc.CutChoose

-- Prove2me | Theorems.Thm_StrategicAlloc_EFXTwoThirds_vstar_efx_iff
-- name    : StrategicAlloc.EFXTwoThirds.vstar_efx_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T15:58:17.855912+00:00
-- url     : https://prove2.me/theorems/ff82a850-4468-4dfe-b816-ac9552ff5299
-- title:
--   Proof of Theorem 4.7, p. 21 — the identical profile (v∗, v∗) has exactly two EFX allocations
-- statement:
--   Let $m\ge 4$, $\varepsilon>0$ with $(m-3)\varepsilon<0.2$, and let both agents have the valuation $v^*$ with $v^*(h_1)=1.2$, $v^*(h_2)=v^*(h_3)=1$ and $v^*(h_j)=\varepsilon$ for $4\le j\le m$. An allocation $(A_1,A_2)$ of $\{h_1,\dots,h_m\}$ is EFX with respect to $(v^*,v^*)$ if and only if it is one of
--
--   $$\mathcal X=(\{h_1,h_4,\dots,h_m\},\{h_2,h_3\}),\qquad \mathcal Y=(\{h_2,h_3\},\{h_1,h_4,\dots,h_m\}).$$
--
--   In the proof of Theorem 4.7 this pins down the allocation produced by any PNE of the mechanism on the instance $(v^*,v^*)$, and hence the value agent 2 receives there.
--
--   **Formalization Note** The good $h_j$ is `j - 1`; $\{h_2,h_3\}$ is the set of goods with index `1` or `2`, and $\{h_1,h_4,\dots,h_m\}$ is its complement. Both directions of "there are only two EFX allocations" are stated. The hypothesis $m\ge 4$ is the proof's context (four goods $h_1,\dots,h_4$ are named there).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 21, §4.2, proof of Theorem 4.7, fourth paragraph

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting
import Definitions.Def_StrategicAlloc_EFXTwoThirds_vstar

namespace StrategicAlloc.EFXTwoThirds

/-- Proof of Theorem 4.7 (p. 21, fourth paragraph): for the identical valuation profile
`v∗ = (v∗, v∗)` with `m ≥ 4`, `ε > 0` and `(m - 3)ε < 0.2`, the only EFX allocations are
`X = ({h_1, h_4, …, h_m}, {h_2, h_3})` and `Y = ({h_2, h_3}, {h_1, h_4, …, h_m})`. -/
theorem vstar_efx_iff {m : ℕ} (hm : 4 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hεm : ((m : ℝ) - 3) * ε < 1 / 5)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) :
    IsEFX (fun _ => vstar ε) A ↔
      A = ![Finset.univ.filter (fun g : Fin m => ¬ (g.val = 1 ∨ g.val = 2)),
            Finset.univ.filter (fun g : Fin m => g.val = 1 ∨ g.val = 2)] ∨
      A = ![Finset.univ.filter (fun g : Fin m => g.val = 1 ∨ g.val = 2),
            Finset.univ.filter (fun g : Fin m => ¬ (g.val = 1 ∨ g.val = 2))] := by sorry

end StrategicAlloc.EFXTwoThirds

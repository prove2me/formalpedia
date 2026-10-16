-- Prove2me | Theorems.Thm_StrategicAlloc_EFXFour_vstar_efx_iff
-- name    : StrategicAlloc.EFXFour.vstar_efx_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T14:14:48.407386+00:00
-- url     : https://prove2.me/theorems/e372dd3d-a4fb-4ac4-b45a-9d46ee84cc7a
-- title:
--   §4.2, p. 20, proof of Theorem 4.5 — v∗ has exactly two EFX allocations, ({h_1, h_4}, {h_2, h_3}) and its symmetric
-- statement:
--   Consider four goods $h_1, h_2, h_3, h_4$ and the identical valuation profile $\mathbf v^* = (v^*, v^*)$ in which both agents value the goods additively by
--   $$
--   v^*(h_1) = 1.2, \qquad v^*(h_2) = v^*(h_3) = 1, \qquad v^*(h_4) = 0.1.
--   $$
--   An allocation $(A_1, A_2)$ of the four goods is EFX with respect to $\mathbf v^*$ if and only if it is one of
--   $$
--   (\{h_1, h_4\}, \{h_2, h_3\}) \qquad\text{or}\qquad (\{h_2, h_3\}, \{h_1, h_4\}).
--   $$
--
--   In the proof of Theorem 4.5 this pins down the allocation at every equilibrium of an always-EFX mechanism on $\mathbf v^*$; in particular, each agent's value there is at most 2.
--
--   **Formalization Note** The goods $h_1, \dots, h_4$ are `0, 1, 2, 3`; $1.2$ and $0.1$ are `6/5` and `1/10`. Both directions of "there are only two EFX allocations" are stated.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 20, proof of Theorem 4.5, Case 3, sentence after the definition of v∗

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXFour

theorem vstar_efx_iff (A : Fin 2 → Finset (Fin 4)) (hA : StrategicAlloc.RRFair.IsAllocation A) :
    StrategicAlloc.CutChoose.IsEFX (fun _ => vstar) A ↔ A = ![{0, 3}, {1, 2}] ∨ A = ![{1, 2}, {0, 3}] := by sorry

end StrategicAlloc.EFXFour

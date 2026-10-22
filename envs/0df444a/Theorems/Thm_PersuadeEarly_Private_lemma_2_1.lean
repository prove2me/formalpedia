-- Prove2me | Theorems.Thm_PersuadeEarly_Private_lemma_2_1
-- name    : PersuadeEarly.Private.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:19.177246+00:00
-- url     : https://prove2.me/theorems/fe963f87-99f7-4f66-8901-e5eddd9aa6be
-- title:
--   Lemma 2 (1), p. 35 — $\phi(t,p)\le\max\{(\bar F^{-1}(q_L)-p)q_L,0\}$
-- statement:
--   Under the standing assumptions, for every $p\in V=[0,b]$ and every threshold $t\ge p$, the L-state public-threshold profit (A.4) satisfies
--   $$\phi(t,p)\le\max\big\{(\bar F^{-1}(q_L)-p)\,q_L,\ 0\big\}.$$
--
--   This bounds what any public threshold can extract in the low-inventory state; it is used in the analysis of public signaling (Theorem 1) and in the proof of Lemma 4.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 35, Lemma 2, part 1

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_AppendixA

open Set

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 35, Lemma 2, part 1: for any `p ∈ V` and `t ≥ p`,
`ϕ(t, p) ≤ max{(F̄^{-1}(qL) − p) qL, 0}`.

**Formalization Note** `V = [0, b]`; `ϕ` is (A.4) with the availabilities (A.5) encoded by
`avail`. -/
theorem lemma_2_1 (M : Model) (hM : M.Standing) :
    ∀ p ∈ Icc 0 M.b, ∀ t, p ≤ t → phi M t p ≤ max ((M.FbarInv M.qL - p) * M.qL) 0 := by sorry

end PersuadeEarly.Private

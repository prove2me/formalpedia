-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_shops_encoding_reduction
-- name    : TwoAgentSched.Shops.shops_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:14.428969+00:00
-- url     : https://prove2.me/theorems/447fa1fe-d04a-4e1d-9b01-e1dc86a47518
-- title:
--   Theorems 10.1 and 10.2 — Polynomial-Time Binary Encoding Reductions for Two-Agent Flow and Open Shops
-- statement:
--   Rescaling the flow shop construction $\mathrm{flowInst}(p)$ by $2(k + 1)$ and the open shop construction $\mathrm{openInst}(p)$ by $2$ yields natural-number instances in $\mathrm{flowLang}$ and $\mathrm{openLang}$ whose binary codes over $\mathrm{BSym}$ are computable in polynomial time from $\mathrm{encNats}(p)$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, Scheduling problems with two competing agents, Operations Research 52(2), pp. 238–239, Theorems 10.1 and 10.2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_Shops_Construction

namespace TwoAgentSched.Shops

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time binary encoding reductions for Theorems 10.1 and 10.2 (Agnetis et al. 2004,
pp. 238–239): rescaling `flowInst p` by `2(k + 1)` and `openInst p` by `2` yields natural-number
shop instances whose binary codes in `flowLang` and `openLang` are computable in polynomial time
from `encNats p`. -/
theorem shops_encoding_reduction :
    (∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ p : List ℕ, Even p.sum ∧ (2 ≤ p.sum ∨ p.length ≤ 1) ∧
            (flowInst p).FlowYes (flowQA p) (flowQB p) ∧ x = encNats p) ∨
          (∃ p : List ℕ, p.sum = 0 ∧ x = encNats p)) ↔ f x ∈ flowLang) ∧
    (∃ g : List BSym → List BSym, PolyTimeComputable g ∧
      ∀ x : List BSym,
        (∃ p : List ℕ, (openInst p).OpenYes (openQA p) (openQB p) ∧ x = encNats p) ↔
          g x ∈ openLang) := by sorry

end TwoAgentSched.Shops

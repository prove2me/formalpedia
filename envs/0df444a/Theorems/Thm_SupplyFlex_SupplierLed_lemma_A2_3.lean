-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_lemma_A2_3
-- name    : SupplyFlex.SupplierLed.lemma_A2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:59.86075+00:00
-- url     : https://prove2.me/theorems/79a8d752-e934-458b-a6bd-8b63d1e79018
-- title:
--   Lemma A2.3, App. A2 p. 4 (PDF 43) — problem (A2.8) has an optimal solution
-- statement:
--   In a standard model, the supplier's recast problem (A2.8),
--   $$\max_{0 \le \hat q \le q}\ \hat\Pi^S(q, \hat q) = r\bigl[pq\bar F(q) + (1-p)\hat q \bar F(\hat q)\bigr] - (1-p)s\hat q - cq \quad\text{s.t.}\quad r\bigl[pq\bar F(q) + (1-p)\hat q \bar F(\hat q)\bigr] \le (pq + (1-p)\hat q)s,$$
--   has an optimal solution: a feasible $(q, \hat q)$ whose objective value is at least that of every feasible point.
--
--   Existence is the first step of the characterization of (A2.8) in Lemma A2.2, and hence of the supplier's optimal contract with $w \le s$. The paper omits the proof.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A2 p. 4 (PDF 43), Lemma A2.3 and problem (A2.8)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Lemma A2.3, App. A2 p. 4 (PDF 43): problem (A2.8) has an optimal solution. -/
theorem lemma_A2_3 (M : Model) (hM : M.Std) :
    ∃ x ∈ a28Feasible M, ∀ x' ∈ a28Feasible M, a28Obj M x' ≤ a28Obj M x := by sorry

end SupplyFlex.SupplierLed

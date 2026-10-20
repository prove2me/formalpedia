-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_qo_lt_qc
-- name    : SupplyFlex.SupplierLed.qo_lt_qc
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T05:37:57.387001+00:00
-- url     : https://prove2.me/theorems/2f8859e9-d831-426f-8660-dd88caa05fea
-- title:
--   Equations (2)–(4), p. 10 — when $w^o>s$, every solution $\check q\ge\hat q^*$ of (4) exceeds $q^o$
-- statement:
--   Let $M$ be a standard model, and let $q^o$, $\hat q^*$ be as in equations (2) and (3): $q^o\ge 0$ with $rpG(q^o)=c$, and $\hat q^*\ge 0$ with $rG(\hat q^*)=s$ when $s\le r$ ($\hat q^*=0$ when $s>r$). Suppose $w^o>s$, where
--   $$w^o=\frac{r\bigl(pq^o\bar F(q^o)+(1-p)\hat q^*\bar F(\hat q^*)\bigr)}{pq^o+(1-p)\hat q^*}.$$
--   If $\check q\ge\hat q^*$ solves equation (4),
--   $$r\bigl(p\check q\,\bar F(\check q)+(1-p)\hat q^*\bar F(\hat q^*)\bigr)=s\bigl(p\check q+(1-p)\hat q^*\bigr),$$
--   then
--   $$q^o<\check q.$$
--
--   In Scenario 2 of Theorem 3 the supplier induces the order $\check q$ rather than $q^o$, because the unconstrained choice $(q^o,\hat q^*)$ violates $w\le s$. The inequality says this binding constraint raises the order. With (A1.16) it gives the buyer's half of Theorem 6 when $\kappa^*=\check q$.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break: sharing supply risk using the supply-flexibility contract (SSRN 3143238; M&SOM 23(5) 2021), p. 10 eqs. (2)–(4) and Assumption 2 (IGFR); the ordering q° < q̌ used for the case κ* = q̌ of Theorems 3–6

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Equations (2)–(4), p. 10: when `w° > s`, every solution `q̌ ≥ q̂*` of (4) exceeds `q°`. -/
theorem qo_lt_qc (M : Model) (hM : M.Std) (qo qh qc : ℝ)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hs : M.s < wo M qo qh)
    (hqc : qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) :
    qo < qc := by sorry

end SupplyFlex.SupplierLed

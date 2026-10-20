-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_root_qc_exists
-- name    : SupplyFlex.SupplierLed.root_qc_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T05:38:03.508547+00:00
-- url     : https://prove2.me/theorems/bd4d3a8c-7a6c-44f2-9bee-9f5f9525242d
-- title:
--   Equation (4), p. 10 — when $w^o>s$, equation (4) has a solution $\check q\ge\hat q^*$
-- statement:
--   Let $M$ be a standard model. Let $q^o\ge 0$ solve $rpG(q)=c$ (equation (2)), and let $\hat q^*\ge 0$ solve $rG(\hat q)=s$ (equation (3)) when $s\le r$, with $\hat q^*=0$ when $s>r$. Suppose
--   $$w^o=\frac{r\bigl(pq^o\bar F(q^o)+(1-p)\hat q^*\bar F(\hat q^*)\bigr)}{pq^o+(1-p)\hat q^*}>s.$$
--   Then there is a $\check q\ge\hat q^*$ solving equation (4):
--   $$r\bigl(p\check q\,\bar F(\check q)+(1-p)\hat q^*\bar F(\hat q^*)\bigr)=s\bigl(p\check q+(1-p)\hat q^*\bigr).$$
--
--   This is the existence of the quantity $\check q$ used in the paper's $\kappa^*$, Theorem 3 and Lemma A2.2. The paper takes it for granted.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break: sharing supply risk using the supply-flexibility contract (SSRN 3143238; M&SOM 23(5) 2021), p. 10 eq. (4): existence of the solution q̌ ≥ q̂* (presupposed in the definition of κ* and in Lemma A2.2)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Equation (4), p. 10: when `w° > s`, equation (4) has a solution `q̌ ≥ q̂*`. -/
theorem root_qc_exists (M : Model) (hM : M.Std) (qo qh : ℝ)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hs : M.s < wo M qo qh) :
    ∃ qc : ℝ, qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh) := by sorry

end SupplyFlex.SupplierLed

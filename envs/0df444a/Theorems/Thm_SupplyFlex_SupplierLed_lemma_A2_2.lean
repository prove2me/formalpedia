-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_lemma_A2_2
-- name    : SupplyFlex.SupplierLed.lemma_A2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:45.501784+00:00
-- url     : https://prove2.me/theorems/23c910b8-7f36-423a-83bc-0e3c22ca1316
-- title:
--   Lemma A2.2, App. A2 p. 4 (PDF 43) (corrected: unique only for p < 1) — the optimal solution of problem (A2.8)
-- statement:
--   In a standard model, let $q^o \ge 0$ solve $r p\,G(q) = c$ (equation (2)); let $\hat q^* \ge 0$ solve $r\,G(\hat q) = s$ (equation (3)) when $s \le r$, with $\hat q^* = 0$ when $s > r$; and, when
--   $$r\bigl(p q^o \bar F(q^o) + (1-p)\hat q^* \bar F(\hat q^*)\bigr) > s\bigl(p q^o + (1-p)\hat q^*\bigr),$$
--   let $\check q \ge \hat q^*$ solve $r\bigl(p q \bar F(q) + (1-p)\hat q^* \bar F(\hat q^*)\bigr) = s\bigl(pq + (1-p)\hat q^*\bigr)$ (equation (4)). Define
--   1. $x^* = (q^o, 0)$ if $s > r$;
--   2. $x^* = (q^o, \hat q^*)$ if $s \le r$ and $r\bigl(p q^o \bar F(q^o) + (1-p)\hat q^* \bar F(\hat q^*)\bigr) \le s\bigl(p q^o + (1-p)\hat q^*\bigr)$;
--   3. $x^* = (\check q, \hat q^*)$ otherwise.
--
--   Then $x^*$ is feasible for problem (A2.8) and maximises its objective $\hat\Pi^S$ over the feasible set; when $p < 1$ it is the unique maximiser.
--
--   The lemma solves the supplier's contract problem in the region $w \le s$, after the change of variables $\hat q = \bar\beta q$.
--
--   **Formalization Note.** The paper says "the optimal solution". At $p = 1$ the objective does not depend on $\hat q$, so the maximiser is not unique; uniqueness is claimed only for $p < 1$. The roots are arguments with hypotheses saying they solve (2)–(4).
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A2 p. 4 (PDF 43), Lemma A2.2, (A2.8)–(A2.11); eqs. (2)–(4), p. 10

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Lemma A2.2, App. A2 p. 4 (PDF 43) (corrected: "the" optimal solution is unique only for
`p < 1`). -/
theorem lemma_A2_2 (M : Model) (hM : M.Std) (qo qh qc : ℝ)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hqc : M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) :
    let xs : ℝ × ℝ :=
      if M.r < M.s then (qo, 0)
      else if M.r * (M.p * qo * Fbar M.f qo + (1 - M.p) * qh * Fbar M.f qh) ≤
          M.s * (M.p * qo + (1 - M.p) * qh) then (qo, qh)
      else (qc, qh)
    xs ∈ a28Feasible M ∧ (∀ x ∈ a28Feasible M, a28Obj M x ≤ a28Obj M xs) ∧
      (M.p < 1 → ∀ x ∈ a28Feasible M, a28Obj M x = a28Obj M xs → x = xs) := by sorry

end SupplyFlex.SupplierLed

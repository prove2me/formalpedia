-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_lemma_2
-- name    : StrategicRFx.Benefit.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:11.810049+00:00
-- url     : https://prove2.me/theorems/10a407d8-ca93-4fcb-91af-866f34e3c385
-- title:
--   Lemma 2, p. 18 — the buyer accepts both offers iff π̃_j ≤ θ_j(Π − π̃_i − Π^{-j})^+ for {i,j} = {1,2}
-- statement:
--   Let $\tilde\pi_1,\tilde\pi_2\ge 0$ be the suppliers' offers. The buyer accepts both offers without renegotiation if and only if
--   $$\tilde\pi_j\le\theta_j\big(\Pi-\tilde\pi_i-\Pi^{-j}\big)^+\qquad\text{for }\{i,j\}=\{1,2\}.$$
--   Furthermore, if the buyer accepts $\tilde\pi_1$ and $\tilde\pi_2$, she accepts $\tilde\pi_1'$ and $\tilde\pi_2'$ for any $\tilde\pi_1'\in[0,\tilde\pi_1]$ and $\tilde\pi_2'\in[0,\tilde\pi_2]$.
--
--   This lemma turns the buyer's negotiation behaviour into an explicit region of offers; the proof of Theorem 5 bounds the buyer's profit over that region by the program [Q].
--
--   **Formalization Note** "The buyer accepts both offers" is the predicate defined in the setting: no negotiation option (either leader, accept or reject the leader's offer, any solution of [RFx-i]) gives her more than $\Pi-\tilde\pi_1-\tilde\pi_2$; ties go to accepting both, as on p. 16. It is defined from the Nash programs (8)–(12), not from the closed-form region, so the equivalence has content.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma 2, p. 18 (proof p. ec14)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Lemma 2 (p. 18). The buyer accepts both offers without renegotiation iff
`π̃_j ≤ θ_j (Π - π̃_i - Π^{-j})^+` for `{i, j} = {1, 2}`; and if she accepts `π̃_1` and `π̃_2`,
she accepts `π̃'_1` and `π̃'_2` for any `π̃'_1 ∈ [0, π̃_1]`, `π̃'_2 ∈ [0, π̃_2]`. -/
theorem lemma_2 (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (AcceptsBoth P t ↔
      ∀ i, t (other i) ≤ P.θ (other i) * max (P.Pi - t i - P.PiEx (other i)) 0) ∧
    (AcceptsBoth P t →
      ∀ t' : Fin 2 → ℝ, (∀ i, 0 ≤ t' i ∧ t' i ≤ t i) → AcceptsBoth P t') := by sorry

end StrategicRFx.Benefit

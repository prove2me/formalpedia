-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_lemma_5
-- name    : StrategicRFx.Benefit.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:04.510662+00:00
-- url     : https://prove2.me/theorems/c2518df2-4261-4511-9a98-1767ad274034
-- title:
--   Lemma 5, p. 24 — leader's offer rejected at optimality: supplier i earns π_i > θ_i(Π − Π^{-i})
-- statement:
--   Let the offers $\tilde\pi_1,\tilde\pi_2\ge 0$ be given and suppose that, at optimality, the buyer first negotiates with supplier $i$ and rejects his offer $\tilde\pi_i$; let $(\pi_i,\pi_0^{-j})$ be the solution of [RFx-i] she reaches. Then supplier $i$'s negotiated profit satisfies
--   $$\pi_i>\theta_i\big(\Pi-\Pi^{-i}\big).$$
--
--   The strict inequality is where submodularity of the supply chain profit (Assumption 2, through $\Pi<\Pi^{-2}(q_1^o)+\Pi^{-1}(q_2^o)$) enters; it is used to show that rejecting the leader's offer is never better for the buyer than accepting both offers in the region of Lemma 2.
--
--   **Formalization Note** "At optimality" is as in Lemma 4, with the leader's offer rejected ($D_i=0$). Only the last sentence of the lemma is formalized: the claim "at optimal, the buyer rejects $\tilde\pi_j$" holds only under the paper's tie-breaking rules (a numerical check found a tie with an accept option where it fails without them), and the piecewise closed form of $\pi_i$ and the "Moreover" sentence are not stated.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma 5, p. 24 (proof pp. ec10–ec14)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Lemma 5 (p. 24), last sentence. Suppose that at optimality the buyer first rejects the
offer `π̃_i`. Then supplier `i`'s negotiated profit satisfies `π_i > θ_i (Π - Π^{-i})`. -/
theorem lemma_5 (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i : Fin 2) (π π' : ℝ) (hopt : IsBuyerOptimal P t i false π π') :
    P.θ i * (P.Pi - P.PiEx i) < π := by sorry

end StrategicRFx.Benefit

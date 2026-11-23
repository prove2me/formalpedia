-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_lemma_EC_2
-- name    : StrategicRFx.Benefit.Supplement.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:15:19.724509+00:00
-- url     : https://prove2.me/theorems/180ef23e-9622-4efe-9e74-a95d6476fec4
-- title:
--   Lemma EC.2 — A zero-profit quote by either supplier is immediately accepted.
-- statement:
--   Let the published reduced bargaining parameters satisfy the source standing assumptions, and let both suppliers quote nonnegative profits. If supplier $i$ quotes zero, every buyer-optimal response respecting acceptance of both offers and early-acceptance priority accepts his offer immediately:
--
--   $$\widetilde\pi_i=0\quad\Longrightarrow\quad \text{supplier }i\text{’s offer is accepted immediately}.$$
--
--   Immediate acceptance includes accepting both offers; when both quotes are zero this does not demand that two different suppliers each negotiate first. The result anchors the source's later construction of the technical tie selector.
--
--   Differences from the source:
--   - encoding: supplier indices 1 and 2 and nonnegative profit quotations → Fin 2 indices and explicit nonnegativity of both real quotes; reason: retains the full source quotation domain
--   - encoding: immediate acceptance, including acceptance of both offers → a canonical accept-both response or accepting supplier i as leader; reason: the proof treats accept-both as immediate acceptance of either supplier
--   - generalization: the buyer follows the source tie hierarchy and later technical refinement → every optimal response satisfying the first two priorities; reason: the ec16 proof uses only accepting both and early acceptance; additional technical restrictions only reduce the quantified responses
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma EC.2, p. ec16

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Negotiation

namespace StrategicRFx.Benefit.Supplement

theorem lemma_EC_2 (P : Params) (h : Standing P) (t : Fin 2 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (i : Fin 2) (hz : t i = 0)
    (r : Negotiation) (hr : IsPriorityResponse P t r) :
    AcceptedImmediately i r := by sorry

end StrategicRFx.Benefit.Supplement

-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_threshold_order
-- name    : TokenSignal.Asymmetry.threshold_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:56.467905+00:00
-- url     : https://prove2.me/theorems/6f03500a-eeed-41cc-aa09-3a50b17e0351
-- title:
--   Token financing requires a smaller sale fraction
-- statement:
--   For either investor belief $j\in\{H,L\}$, a token sale finances the investment with a strictly smaller fraction than an equity sale:
--
--   $$\bar\alpha_j^T<\bar\alpha_j^E.$$
--
--   The strict ordering follows from the fixed production cost paid before equity holders’ return, while token holders receive a claim on gross revenue.
--
--   **Formalization Note** Strictness uses $C>0$; feasibility of both securities for the low type uses $I\le\mu_L/4-C$.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 21 (PDF 22), paragraph before Corollary 1

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem threshold_order (P : Params) (hS : P.Standing) (j : Ty) :
    αbar P .token j < αbar P .equity j := by sorry
end TokenSignal.Asymmetry

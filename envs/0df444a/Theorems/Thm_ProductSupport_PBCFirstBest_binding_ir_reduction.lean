-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_binding_ir_reduction
-- name    : ProductSupport.PBCFirstBest.binding_ir_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.239064+00:00
-- url     : https://prove2.me/theorems/4b41df9b-80ee-4af1-bbb6-9a83926b3812
-- title:
--   Proof of Proposition 1(ii) — binding IR and reduced PBC objective
-- statement:
--   Fix one type with failure rate $\lambda>0$, reservation payoff $M$, repair rate $\mu>\lambda$, and price $v$. If its customer payoff is at least $M$, then
--   $$
--   \pi_s^P(v,\mu)\leq-M+r-c_r\lambda-\frac{r\lambda}{\mu}-c\mu.
--   $$
--   At the price $v=r+M\mu/(\lambda-\mu)$, the customer payoff equals $M$ and the supplier payoff equals the displayed upper bound. This is the binding-IR reduction (B.6)–(B.7) used to solve the full-information PBC problem.
--
--   **Formalization Note** The inequalities $0<\lambda<\mu$ make the uptime positive and the price formula well-defined. The binding price is an algebraic candidate; this statement does not assert that it is strictly positive.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), supplement p. 3 (PDF 36), proof of Proposition 1(ii), (B.5)–(B.7)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem binding_ir_reduction (P : Params) (hS : P.Standing)
    (lam M mu v : ℝ) (hlam : 0 < lam) (hmu : lam < mu)
    (hIR : M ≤ custPayoff P lam ⟨v, mu⟩) :
    suppPayoff P lam ⟨v, mu⟩ ≤
      -M + P.r - P.cr * lam - P.r * lam / mu - P.c * mu ∧
    custPayoff P lam ⟨vBinding P lam M mu, mu⟩ = M ∧
    suppPayoff P lam ⟨vBinding P lam M mu, mu⟩ =
      -M + P.r - P.cr * lam - P.r * lam / mu - P.c * mu := by sorry

end ProductSupport.PBCFirstBest

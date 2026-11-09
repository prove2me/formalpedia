-- Prove2me | Theorems.Thm_Pr6453_outer_ledger
-- name    : Pr6453.outer_ledger
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T16:04:58.623727+00:00
-- url     : https://prove2.me/theorems/b55a79fc-facd-45b8-9f1e-523b0f691859
-- title:
--   PR #6453: the outer ledger at $\kappa = 0.003287014$
-- statement:
--   The outer ledger of the PR #6453 word holds at the claimed saving $\kappa = 1643507/500000000 = 0.003287014$.
--
--   The compiled word prices its nine cost components — the boundary algebraic matrix, the fused Gaussian stage, the global coordinate router, the group bit router, the group scans, the main transform, the microbox face corrections, the polynomial products and the sparse union movement. Each of the nine margins exceeds $\kappa$, and each does so by exactly the slack recorded in the certificate:
--
--   $$\text{margin}_i - \kappa \;=\; \delta_i \;>\; 0, \qquad i = 1,\dots,9,$$
--
--   with the smallest slacks of order $2\times10^{-9}$ (the main transform) and the largest $77$ (the microbox face corrections).
--
--   Around the nine margins the statement records where the claim sits in the exponent line: strictly above the parent composition PR #6417 ($3286849/10^9 = 0.003286849$), strictly below the tested value $3287019/10^9 = 0.003287019$, and the tested value strictly below the certified crossing interval recorded by the certificate, whose lower end is $0.00328701955375063425072028$; finally the claim is strictly below the compiler's complex uniform saving $2876141/875000000$.
--
--   This is the ledger that a machine-level proof consumes once the recursive invoices are formalised: it is what turns "the construction's costs are all strictly cheaper than the saving" into the exponent of the running time.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/RESULT.json (complete_cost.outer.margins, complete_cost.outer.strict_checks, complete_cost.kappa, complete_cost.compiler)

import Definitions.Def_Pr6453_RankMoments

set_option autoImplicit false

namespace Pr6453

theorem outer_ledger :
    (3286849 / 1000000000 : ℝ) < kappa ∧
    (kappa : ℝ) < (3287019 / 1000000000 : ℝ) ∧
    (3287019 / 1000000000 : ℝ) < (82175488843765856268007 / 25000000000000000000000000 : ℝ) ∧
    (kappa : ℝ) < (32212765176990887 / 9800000000000000000 : ℝ) ∧
    (kappa : ℝ) < (32212765130972661 / 9800000000000000000 : ℝ) ∧
    (kappa : ℝ) < (11504559 / 3500000000 : ℝ) ∧
    (kappa : ℝ) < (16106386065486323 / 4900000000000000000 : ℝ) ∧
    (kappa : ℝ) < (699999999 / 700000000 : ℝ) ∧
    (kappa : ℝ) < (32212758176990887 / 9800000000000000000 : ℝ) ∧
    (kappa : ℝ) < (26950000001 / 350000000 : ℝ) ∧
    (kappa : ℝ) < (1399999999 / 1400000000 : ℝ) ∧
    (kappa : ℝ) < (4013462765176990887 / 9800000000000000000 : ℝ) ∧
    (32212765176990887 / 9800000000000000000 : ℝ) - (kappa : ℝ) = (27976990887 / 9800000000000000000 : ℝ) ∧
    (32212765130972661 / 9800000000000000000 : ℝ) - (kappa : ℝ) = (27930972661 / 9800000000000000000 : ℝ) ∧
    (11504559 / 3500000000 : ℝ) - (kappa : ℝ) = (1 / 350000000 : ℝ) ∧
    (16106386065486323 / 4900000000000000000 : ℝ) - (kappa : ℝ) = (17465486323 / 4900000000000000000 : ℝ) ∧
    (699999999 / 700000000 : ℝ) - (kappa : ℝ) = (1744247723 / 1750000000 : ℝ) ∧
    (32212758176990887 / 9800000000000000000 : ℝ) - (kappa : ℝ) = (20976990887 / 9800000000000000000 : ℝ) ∧
    (26950000001 / 350000000 : ℝ) - (kappa : ℝ) = (269488495461 / 3500000000 : ℝ) ∧
    (1399999999 / 1400000000 : ℝ) - (kappa : ℝ) = (6976990897 / 7000000000 : ℝ) ∧
    (4013462765176990887 / 9800000000000000000 : ℝ) - (kappa : ℝ) = (3981250027976990887 / 9800000000000000000 : ℝ) ∧
    (kappa : ℝ) < (2876141 / 875000000 : ℝ) := by
  sorry

end Pr6453

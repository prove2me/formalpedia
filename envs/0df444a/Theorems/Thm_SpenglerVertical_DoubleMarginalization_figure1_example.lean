-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_figure1_example
-- name    : SpenglerVertical.DoubleMarginalization.figure1_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:08.541002+00:00
-- url     : https://prove2.me/theorems/0cdf3e59-5a0c-4d4d-82da-3a309825fde6
-- title:
--   Sections II–III, Figure 1 — P_c = 115, Q = 40, aggregate profit 2,200 vs. P′_c = 100, Q′ = 64, profit 2,560; consumers' surplus rises by 780
-- statement:
--   The numerical example of Figure 1. Stage A faces $D_a(p)=4(40-p)$, stage B faces $D_b(p)=2(90-p)$, and stage C faces the final demand $D_c(p)=\tfrac85(140-p)$. The unit variable costs are $V_a=V_b=V_c=20$. Then:
--
--   1. at cost $V_a=20$, stage A's profit-maximizing price is $P_a=30$, with $D_a(30)=40$;
--   2. at cost $C_b=P_a+V_b=50$, stage B's profit-maximizing price is $P_b=70$, with $D_b(70)=40$;
--   3. at cost $C_c=P_b+V_c=90$, stage C's profit-maximizing price is $P_c=115$; the vertically integrated firm, with cost $C'_c=V_a+V_b+V_c=60$, has profit-maximizing price $P'_c=100$;
--   4. $Q=D_c(115)=40$, $Q'=D_c(100)=64$, $Q''=D_c(60)=128$;
--   5. before integration: stage C's profit $Q(P_c-M_c)=1{,}000$; aggregate variable cost $2{,}400$; aggregate profit $R_aQ+R_bQ+R_cQ=2{,}200$; aggregate sales value $4{,}600$;
--   6. after integration: profit $Q'(P'_c-M'_c)=2{,}560$ and variable expense $3{,}840$;
--   7. the increase in Marshallian consumers' surplus is
--   $$\int_{100}^{115}D_c(x)\,dx=780=Q(P_c-P'_c)+\tfrac12(Q'-Q)(P_c-P'_c).$$
--
--   This is the concrete instance of the goal theorem that the paper works through.
--
--   **Formalization Note** The paper does not print the demand curves' equations. $D_c$ is the line through the three points the text gives, $(Q,P)=(40,115),(64,100),(128,60)$, with price intercept 140 as drawn; $D_a$ and $D_b$ are read off Figure 1 (intercepts 40 and 90, reaching the cost lines 20 and 50 at $Q=80$). Footnote 5's formula is the area of a trapezoid and holds here because $D_c$ is a straight line.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), pp. 348–350, Sections II–III, Figure 1, footnotes 3 and 5; https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem figure1_example :
    IsProfitMax (linearDemand 40 4) 20 30 ∧ linearDemand 40 4 30 = 40 ∧
    IsProfitMax (linearDemand 90 2) (30 + 20) 70 ∧ linearDemand 90 2 70 = 40 ∧
    IsProfitMax (linearDemand 140 (8 / 5)) (70 + 20) 115 ∧
    IsProfitMax (linearDemand 140 (8 / 5)) (20 + 20 + 20) 100 ∧
    linearDemand 140 (8 / 5) 115 = 40 ∧
    linearDemand 140 (8 / 5) 100 = 64 ∧
    linearDemand 140 (8 / 5) 60 = 128 ∧
    (115 - (70 + 20)) * linearDemand 140 (8 / 5) 115 = 1000 ∧
    (20 + 20 + 20) * linearDemand 140 (8 / 5) 115 = 2400 ∧
    (30 - 20) * linearDemand 140 (8 / 5) 115 + (70 - (20 + 30)) * linearDemand 140 (8 / 5) 115
      + (115 - (20 + 70)) * linearDemand 140 (8 / 5) 115 = 2200 ∧
    115 * linearDemand 140 (8 / 5) 115 = 4600 ∧
    (100 - (20 + 20 + 20)) * linearDemand 140 (8 / 5) 100 = 2560 ∧
    (20 + 20 + 20) * linearDemand 140 (8 / 5) 100 = 3840 ∧
    (∫ x in (100 : ℝ)..115, linearDemand 140 (8 / 5) x) = 780 ∧
    linearDemand 140 (8 / 5) 115 * (115 - 100)
      + (linearDemand 140 (8 / 5) 100 - linearDemand 140 (8 / 5) 115) * (115 - 100) * (1 / 2)
      = 780 := by sorry

end SpenglerVertical.DoubleMarginalization

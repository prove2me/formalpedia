-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_vertical_integration_benefits_producer_and_consumer
-- name    : SpenglerVertical.DoubleMarginalization.vertical_integration_benefits_producer_and_consumer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:18.825847+00:00
-- url     : https://prove2.me/theorems/a97cf052-1f5a-4f85-bf6c-9a7e184c505e
-- title:
--   Section III — vertical integration of successive monopolies lowers the final price and raises output, aggregate profit and consumers' surplus
-- statement:
--   Consider three successive stages of production $A\to B\to C$ with fixed proportions (one unit of each stage's product per unit of the next) and constant unit variable costs $V_a,V_b,V_c$. Let $D$ be a non-increasing demand curve for the final product $C$. Stage A sells to stage B at price $P_a$ and stage B sells to stage C at price $P_b$, each with a positive "monopolistic" profit per unit:
--   $$R_a=P_a-V_a>0,\qquad R_b=P_b-(V_b+P_a)>0.$$
--   Without integration, stage C has unit cost $C_c=V_c+P_b$ and charges a profit-maximizing price $P_c$ at that cost; it sells $Q=D(P_c)$ units, and every stage handles the same $Q$ units. A vertically integrated firm has unit cost $C'_c=V_a+V_b+V_c$ and charges a profit-maximizing price $P'_c$ at that cost, selling $Q'=D(P'_c)$. Assume $D$ is differentiable at $P_c$ and $Q>0$. Then
--
--   1. the integrated firm lowers the price: $P'_c<P_c$;
--   2. output rises: $Q<Q'$;
--   3. aggregate "profit" (return above variable expense) rises:
--   $$R_aQ+R_bQ+R_cQ<\big(P'_c-(V_a+V_b+V_c)\big)Q',\qquad R_c=P_c-(V_c+P_b);$$
--   4. consumers' (Marshallian) surplus rises, by at least $Q(P_c-P'_c)$:
--   $$0<\int_{P'_c}^{P_c}D(x)\,dx,\qquad Q\,(P_c-P'_c)\le\int_{P'_c}^{P_c}D(x)\,dx.$$
--
--   Since $V_a+V_b+V_c+R_a+R_b+R_c=P_c$, the left side of item 3 is the chain's aggregate profit $Q[P_c-(V_a+V_b+V_c)]$. This is Spengler's conclusion that "vertical integration, under the conditions assumed, … benefits both producer and consumer": the integrated firm evades the surcharges $R_a+R_b$ imposed upstream, which is the double-marginalization argument against treating vertical integration as illegal per se.
--
--   **Formalization Note** The paper argues on Figure 1 and asserts the result "under all cases conceivable … within the framework here employed"; the statement is for an arbitrary non-increasing demand curve and arbitrary transfer prices with positive markups ($P_a$, $P_b$ need not themselves be profit-maximizing). Prices range over $\mathbb R$. Two readings are added: differentiability of $D$ at $P_c$ (the paper's marginal-revenue reasoning presupposes it; without it a kinked demand curve can leave the price unchanged) and $Q>0$ (the chain trades). The weak versions ($\le$) of items 2 and 3 need neither; the weak version of item 1 still needs $Q>0$ (if $D\equiv0$ every price is profit-maximizing). No linearity, concavity or uniqueness of maximizers is assumed.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), pp. 347–350, Sections I–III (main statement p. 350, restated p. 352, Section IV); https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem vertical_integration_benefits_producer_and_consumer
    (D : ℝ → ℝ) (hD : Antitone D)
    (Va Vb Vc Pa Pb Pc Pc' : ℝ)
    (hRa : 0 < Pa - Va) (hRb : 0 < Pb - (Vb + Pa))
    (hPc : IsProfitMax D (Vc + Pb) Pc)
    (hPc' : IsProfitMax D (Va + Vb + Vc) Pc')
    (hdiff : DifferentiableAt ℝ D Pc) (hQ : 0 < D Pc) :
    Pc' < Pc ∧
    D Pc < D Pc' ∧
    (Pa - Va) * D Pc + (Pb - (Vb + Pa)) * D Pc + (Pc - (Vc + Pb)) * D Pc
      < (Pc' - (Va + Vb + Vc)) * D Pc' ∧
    D Pc * (Pc - Pc') ≤ ∫ x in Pc'..Pc, D x ∧
    0 < ∫ x in Pc'..Pc, D x := by sorry

end SpenglerVertical.DoubleMarginalization

-- Prove2me | Theorems.Thm_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights
-- name    : WeierstrassCurve.variableChange_veluQuotientOfSums_asymWeights
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/bca95448-f44e-56df-a862-ff966a7957c7
-- title:
--   Velu sum quotient is covariant under variable change
-- statement:
--   Let $K$ be a field, let $C$ be an admissible change of variables over $K$ (data $u \in K^{\times}$, $r,s,t \in K$, acting on Weierstrass curves by the usual Mathlib action $C \bullet W$), let $W$ be a Weierstrass curve over $K$, and let $S$ be a finite subset of $K \times K$. Write $G_x(x,y) = 3x^{2} + 2a_2 x + a_4 - a_1 y$ and $G_y(x,y) = -(2y + a_1 x + a_3)$ for the two partial-derivative expressions attached to a curve, and recall that `veluQuotientOfSums` $t'$ $w'$ is the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4 - 5t'$ and $a_6$ by $a_6 - b_2 t' - 7w'$. Assume $S$ is closed under the involution $(x,y) \mapsto (x, -y - a_1 x - a_3)$ coming from $W$, i.e. $(P_1, \mathrm{negY}(P_1,P_2)) \in S$ for all $P \in S$. Then the curve obtained from $C \bullet W$ by the `veluQuotientOfSums` construction with $t'$ the sum of $G_x$ over the image of $S$ under the embedding $P \mapsto (u^{-2}(P_1 - r),\, u^{-3}(P_2 - t - s(P_1 - r)))$ and $w'$ the sum of $P_1 G_x(P) - P_2 G_y(P)$ (gradients taken for $C \bullet W$) over that same image, coincides with $C \bullet$ (the `veluQuotientOfSums` of $W$ formed from the corresponding sums of $G_x$ and of $xG_x - yG_y$ over $S$ itself).
--
--   This is the covariance, under admissible changes of variables, of the quotient curve produced by Vélu's formulas from a negation-closed finite set of kernel points, stated in the shape in which the sums of $G_x$ and $xG_x - yG_y$ (rather than the usual symmetric weights $t$ and $w$) serve as parameters. It allows the quotient by a kernel to be computed in whichever coordinate model is convenient and then transported, and it is used in the treatment of full-kernel quotients and of the modular polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights.lean

import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.variableChange_veluQuotientOfSums_asymWeights {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    (C • W).veluQuotientOfSums
        (∑ P ∈ S.map (vcInvEmbedding C), (C • W).veluGx P.1 P.2)
        (∑ P ∈ S.map (vcInvEmbedding C),
          (P.1 * (C • W).veluGx P.1 P.2 - P.2 * (C • W).veluGy P.1 P.2)) =
      C • (W.veluQuotientOfSums (∑ P ∈ S, W.veluGx P.1 P.2)
        (∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))) := by sorry

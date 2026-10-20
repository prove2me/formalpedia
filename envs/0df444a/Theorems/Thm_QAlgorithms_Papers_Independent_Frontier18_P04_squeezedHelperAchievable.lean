-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P04_squeezedHelperAchievable
-- name    : QAlgorithms.Papers.Independent.Frontier18.P04.squeezedHelperAchievable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:52:33.318214+00:00
-- url     : https://prove2.me/theorems/5bfcde31-2ed7-4f3c-8550-7a171a412eba
-- title:
--   Squeezed helper with homodyne reception achieves the displayed rate
-- statement:
--   Fix $0<\eta\le1$, finite photon budgets $\bar n_A,\bar n_B\ge0$, and a squeeze $z\ge0$ satisfying $\sinh^2z\le\bar n_A$. Alice transmits real quadrature displacements of her fixed squeezed seed; Bob transmits no message and uses the squeezed vacuum with $Z=\operatorname{arsinh}\sqrt{\bar n_B}$. The measured noise has strictly positive variance $[\eta e^{-2z}+(1-\eta)e^{-2Z}]/4$, and Bob's squeezing energy is exactly $\sinh^2Z=\bar n_B$. Homodyne reception and classical block decoding achieve the nonnegative rate
--
--   $$
--   R_1=\frac12\log\!\left(1+\frac{4(\bar n_A-\sinh^2z)}{e^{-2z}+(1-\eta)e^{-2Z}/\eta}\right).
--   $$
--
--   Achievability means membership in the closed operational region of this measured squeezed-seed channel, with arbitrarily small average decoding error and displacement budget $\bar n_A-\sinh^2z$. The zero-squeeze boundary is included by closure, and $\bar n_A=z=0$ gives zero rate. Swapping sender names and replacing $\eta$ by $1-\eta$ gives the symmetric result when Bob's transmissivity is positive. This is an achievable code, without a finite-helper optimality assertion.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, PDF p. 10, §V, (81): helper squeezed-state/homodyne achievable rate

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- arXiv:quant-ph/0506171v2, PDF p.10,(81): Alice's squeezed-state real-displacement
code with a zero-message squeezed Bob helper achieves the displayed homodyne rate.
The zero-squeeze boundary is included by closure. Setting nA=z=0 gives rate zero.
The same universal statement, with sender names exchanged and eta replaced by 1-eta,
gives Bob's symmetric achievable rate whenever Bob's transmissivity is positive. -/
theorem squeezedHelperAchievable (eta nA nB z : ℝ)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hnA : 0 ≤ nA) (hnB : 0 ≤ nB)
    (hz : 0 ≤ z) (hbudget : (Real.sinh z) ^ 2 ≤ nA) :
    0 < helperNoise eta nB z ∧
    (Real.sinh (helperSqueeze nB)) ^ 2 = nB ∧
    0 ≤ helperRate eta nA nB z ∧
    (fun _ : Fin 1 => helperRate eta nA nB z) ∈ helperCapacity eta nA nB z := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P04

end

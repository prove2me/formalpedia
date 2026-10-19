-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_strictUnassistedGap
-- name    : QAlgorithms.Papers.Independent.Information100.P58.strictUnassistedGap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:16:53.16025+00:00
-- url     : https://prove2.me/theorems/0adce874-caaa-4446-94dd-da97d89fb73d
-- title:
--   Strict gap for four qubit erasure transmissions
-- statement:
--   Let $0<p<1$. Write $P_{\rm succ}^{*,\rm nf}(4,4)$ for the optimal uniform-message success of four-message codes using four qubit erasure-channel transmissions without feedback. The codewords may be arbitrary mixed states entangled across all four inputs, and the receiver may use any collective POVM. Then
--
--   $$P_{\rm succ}^{*,\rm nf}(4,4)<\sum_{k=0}^4\binom4k(1-p)^kp^{4-k}\min\{1,2^k/4\}.$$
--
--   This is a strict inequality for the operational optimum, not merely nonexistence of an equality-attaining code. Neither endpoint channel is included.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 24, Theorem 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Theorem 6.1, PDF pp.24–25: strict optimum gap, with arbitrary mixed entangled inputs and collective POVMs. -/
theorem strictUnassistedGap (p : ℝ) (hp0 : 0<p) (hp1 : p<1) :
    quantumOptimum 4 2 4 p < dimensionSuccess 4 2 p 4 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58

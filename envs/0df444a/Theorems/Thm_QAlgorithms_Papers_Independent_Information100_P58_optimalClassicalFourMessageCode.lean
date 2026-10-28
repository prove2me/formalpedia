-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_optimalClassicalFourMessageCode
-- name    : QAlgorithms.Papers.Independent.Information100.P58.optimalClassicalFourMessageCode
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:18:08.109954+00:00
-- url     : https://prove2.me/theorems/cd6c1ffc-53f4-4b8a-a918-cfdff6bf0297
-- title:
--   Optimal four-message classical binary erasure code
-- statement:
--   For $0\le p\le1$, consider all classical no-feedback codes with four equiprobable messages and four binary erasure-channel uses. Randomized encoders and decoders are included in both optimizations. The optimal average success and optimal worst-message success both equal
--
--   $$P_{\rm cl}^*(p)=s_{4,2,p}(4)-\frac12p^2(1-p)^2,$$
--
--   where $s_{4,2,p}(4)=\sum_{k=0}^4\binom4k(1-p)^kp^{4-k}\min\{1,2^k/4\}$. The deterministic code $(x,y)\mapsto(x,y,x\oplus y,x)$, decoded uniformly among compatible messages, achieves this value for every individual message. Repeated words are allowed in the class of competing codes.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 28, Theorem 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Theorem 7.2, PDF pp.28–29: randomized classical optimum, both criteria, and explicit simultaneous attainment. -/
theorem optimalClassicalFourMessageCode (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    classicalOptimum 4 2 4 p false = dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 ∧
    classicalOptimum 4 2 4 p true = dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 ∧
    ∀ m, deterministicIndividual p repeatedParity m = dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58

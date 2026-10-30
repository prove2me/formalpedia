-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_entropyPower_photon_concave
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.entropyPower_photon_concave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:48:53.393034+00:00
-- url     : https://prove2.me/theorems/d802ed95-1e2f-4ac0-ad22-2aad40efc9ca
-- title:
--   Theorem 6: concavity of entropy power and entropy photon number
-- statement:
--   Let $d\ge2$ and let $H$ denote von Neumann entropy in nats on normalized $d$-dimensional states, with its continuous zero-eigenvalue convention. Set $E_c(\rho)=\exp(cH(\rho))$ and $N_c(\rho)=g^{-1}(cH(\rho))$, where $g(x)=(x+1)\log(x+1)-x\log x$ on $x\ge0$. Then
--   $$
--   E_c\text{ is concave for }0\le c\le(\log d)^{-2},\qquad
--   N_c\text{ is concave for }0\le c\le(d-1)^{-1}.
--   $$
--   Concavity means the usual inequality for every two density matrices and every convex weight. Both statements include pure and uniform states and $c=0$. These are the two concavity inputs to the qudit EPIs.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 7, Theorem 6: concavity of entropy power and entropy photon number

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.7, Theorem 6, proved pp.23–25: both concavity clauses with their distinct ranges. -/
theorem entropyPower_photon_concave {d : ℕ} (hd : 2 ≤ d) :
    (∀ c : ℝ, 0 ≤ c → c ≤ 1 / (Real.log (d : ℝ)) ^ 2 →
      StateConcave (quditEntropyPower (d := d) c)) ∧
    (∀ c : ℝ, 0 ≤ c → c ≤ 1 / ((d : ℝ) - 1) →
      StateConcave (quditEntropyPhotonNumber (d := d) c)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end

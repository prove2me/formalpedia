-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_renyi_epi
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.renyi_epi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:50:29.946853+00:00
-- url     : https://prove2.me/theorems/6b626abc-f18b-4993-8e41-d83b1161ced4
-- title:
--   Unnumbered Rényi-entropy EPI following Corollary 7; corrected (3.9)
-- statement:
--   Let $d\ge1$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   For $0\le\alpha<1$, use the standard natural-log Rényi entropy
--   $$H_\alpha(\tau)=\frac{\log\operatorname{Tr}(\tau^\alpha)}{1-\alpha}\quad(0<\alpha<1),\qquad H_0(\tau)=\log\operatorname{rank}\tau.$$
--   Then
--   $$H_\alpha(\rho\boxplus_a\sigma)\ge aH_\alpha(\rho)+(1-a)H_\alpha(\sigma).$$
--   This extends the EPI to Rényi entropies, including singular inputs. The sign in printed (3.9) is corrected as explained in the notes.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 7, Unnumbered Rényi-entropy EPI following Corollary 7; corrected (3.9)

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

/-- PDF pp.7–8, unnumbered extension: Renyi EPI for 0 <= alpha < 1.
Printed (3.9) has 1/(alpha-1); changed to 1/(1-alpha) in renyiNats because the printed
sign disproves this EPI for orthogonal pure qubits at a=alpha=1/2. -/
theorem renyi_epi {d : ℕ} (hd : 0 < d) (alpha : ℝ)
    (halpha : alpha ∈ Set.Ico (0 : ℝ) 1) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a * renyiNats alpha rho + (1 - a) * renyiNats alpha sigma ≤
      renyiNats alpha (quditAddition a rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end

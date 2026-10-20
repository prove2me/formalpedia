-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_security_dimension_scaling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.security_dimension_scaling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:30:12.146328+00:00
-- url     : https://prove2.me/theorems/c8a09fb1-3e51-4f5a-81e5-3a4d6cd4994f
-- title:
--   Remark 4: necessity of logarithmic dimension dependence
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $d\ge2$ and $0\le a\le1$. Give each equal key outcome $ii$ probability $(1-a)/d$ and Eve state $|00\rangle\langle00|$, and each unequal outcome $ij$ probability $a/(d^2-d)$ and Eve state $|ij\rangle\langle ij|$. This is a normalized ccq ensemble. For its state $\Omega$ and the comparison $\Omega_{\rm ideal}=d^{-1}\sum_i|ii\rangle\langle ii|\otimes|00\rangle\langle00|$,
--
--   $$\|\Omega-\Omega_{\rm ideal}\|_1=2a,\qquad\chi(\Omega)=h_2(a)+a\log_2(d^2-d).$$
--
--   The comparison fixes Eve at $|00\rangle$, rather than the actual average Eve state. This exhibits the logarithmic dimension dependence of Holevo information.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 33, Remark 4: necessity of logarithmic dimension dependence

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.33, Remark 4, Eq.(215): Eve in the comparison state is fixed at |00>,
NOT the average Eve marginal of the real state when epsilon is nonzero. -/
theorem security_dimension_scaling (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a : ℝ) (ha : 0 ≤ a) (haone : a ≤ 1) :
    IsEnsemble (scalingWeights d a) (scalingEve d) ∧
    traceNorm (cqState (scalingWeights d a) (scalingEve d) -
      idealCCQ (d := d) (pureDensity (ket ((0,0) : Key d)))) = 2*a ∧
    ensembleHolevoBits (scalingWeights d a) (scalingEve d) = binEntropy2 a + a*logBits ((d:ℝ)^2-d) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end

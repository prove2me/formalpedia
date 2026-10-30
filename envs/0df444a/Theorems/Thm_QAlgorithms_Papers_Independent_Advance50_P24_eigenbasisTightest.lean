-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_eigenbasisTightest
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.eigenbasisTightest
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:05:40.967824+00:00
-- url     : https://prove2.me/theorems/03261bdc-a389-44c0-8806-88e3ddca1b2f
-- title:
--   Eigenbasis attains the largest second-moment scalar bound
-- statement:
--   Let $m\ge1$, $N\ge0$, and let $A$ be an $m\times m$ complex positive contraction: $A\succeq0$ and $I-A\succeq0$. Write $\lambda(A)$ for its eigenvalues, including multiplicities, and let $L^M$ be the optimized lower bound in nats. For every unitary input basis $U$,
--
--   $$L^M(\operatorname{diag}(U^\dagger A U),N)\le L^M(\lambda(A),N).$$
--
--   Equality holds for the orthonormal eigenbasis constructed by the spectral theorem. Thus the eigenbasis attains the tightest scalar second-moment bound obtainable by choosing a basis. Expected Gram matrices in the application are positive contractions; no temporal fading capacity is defined here.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 5, Theorem 6 remarks: eigenbasis gives the tightest second-moment lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 6 remarks, PDF p.5: the eigenbasis gives the largest second-moment
scalar bound among all input bases. The matrix is a positive contraction, as
is the expected Gram matrix in the application. The attaining basis is computed
by the spectral theorem, rather than supplied as an optimizing hypothesis. -/
theorem eigenbasisTightest {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin m) ℂ) (hpos : A.PosSemidef)
    (hcontract : (1 - A).PosSemidef) (N : ℝ) (hN : 0 ≤ N) :
    (∀ U : Matrix.unitaryGroup (Fin m) ℂ,
      parallelLower (unitaryBasisDiagonal A U) N ≤ parallelLower hpos.isHermitian.eigenvalues N) ∧
    parallelLower (unitaryBasisDiagonal A hpos.isHermitian.eigenvectorUnitary) N =
      parallelLower hpos.isHermitian.eigenvalues N := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end

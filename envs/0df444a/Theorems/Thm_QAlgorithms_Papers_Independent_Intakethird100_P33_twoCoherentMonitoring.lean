-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_twoCoherentMonitoring
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.twoCoherentMonitoring
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:53:02.60157+00:00
-- url     : https://prove2.me/theorems/6781a07e-e19f-4a9c-9b84-f701e8480d7b
-- title:
--   III.C.3: cross-pair counting preserves boundary coherence and destroys decoy coherence, (23)
-- statement:
--   Take $n\ge0$ source blocks with symbols 0, 1, or decoy, each occupied bin carrying coherent amplitude $\sqrt{x}$ for $x>0$ and each blocked bin vacuum. On every disjoint cross-boundary late/early pair $(2k,2k+1)$, perform a nondemolition measurement of the total photon number and discard the measurement result. The resulting density retains a number-basis matrix element exactly when its bra and ket have the same total in every measured pair. The outer unpaired bins are untouched.
--
--   Both the original and counted full-Fock densities are normalized. For each occupied 1,0 boundary, the required number moments converge and the intrinsic monitor fluxes and contrast are
--
--   $$
--   F_1=x,\quad F_2=0,\quad V_{10}=1.
--   $$
--
--   For each decoy block strictly inside the train, its early and late bins belong to different measured pairs, and
--
--   $$
--   F_1=F_2=x/2,\quad V_d=0.
--   $$
--
--   The summed flux in each ratio is positive. Empty trains are allowed, with no tested pairs. The restriction to internal decoys avoids endpoint artifacts in the finite train.
--
--   This constructs the total-number attack rather than assuming its visibility response. It is separate from the conservative information assignment (22) and does not claim exact count preservation for an operational attack mixture.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 6, III.C.3, Fig.3 and (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P33

open scoped BigOperators ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity rankOne)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P48 (vacuumAmplitude)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P34
  (TwoModeFock fockKet photonMean)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (coherentPair coherentPairCoefficients)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.5-6, Fig.3 and (23): evaluated nonselective nondemolition counting on
successive disjoint shifted pairs. Cross-boundary 1,0 coherence survives, while
internal decoy coherence vanishes. The finite train's endpoints are excluded
only from the decoy test that needs two distinct measured pairs. No information
assignment from (22), count-preserving mixture, or detector probability is assumed. -/
theorem twoCoherentMonitoring (n : ℕ) (w : Fin n → Fin 3) (x : ℝ) (hx : 0 < x) :
    IsDensity (trainDensity w x) ∧ IsDensity (crossCounting w x) ∧
    (∀ k : Fin (n - 1), w (boundaryLeft k) = 1 → w (boundaryRight k) = 0 →
      let i := (boundaryLeft k, true)
      let j := (boundaryRight k, false)
      FinitePairMoments (crossCounting w x) i j ∧
      monitorFlux (crossCounting w x) i j 0 = x ∧
      monitorFlux (crossCounting w x) i j 1 = 0 ∧
      0 < monitorFlux (crossCounting w x) i j 0 + monitorFlux (crossCounting w x) i j 1 ∧
      opticalVisibility (crossCounting w x) i j = 1) ∧
    (∀ k : Fin n, 0 < k.val → k.val + 1 < n → w k = 2 →
      FinitePairMoments (crossCounting w x) (k, false) (k, true) ∧
      monitorFlux (crossCounting w x) (k, false) (k, true) 0 = x / 2 ∧
      monitorFlux (crossCounting w x) (k, false) (k, true) 1 = x / 2 ∧
      0 < monitorFlux (crossCounting w x) (k, false) (k, true) 0 +
        monitorFlux (crossCounting w x) (k, false) (k, true) 1 ∧
      opticalVisibility (crossCounting w x) (k, false) (k, true) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end

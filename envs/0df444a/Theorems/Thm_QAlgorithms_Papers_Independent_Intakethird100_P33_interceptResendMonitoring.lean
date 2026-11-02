-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_interceptResendMonitoring
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.interceptResendMonitoring
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:52:21.37019+00:00
-- url     : https://prove2.me/theorems/67d31168-783a-46b1-b6cc-77831c09e5c3
-- title:
--   III.C.2: intercept-resend destroys both checked coherences, (21)
-- statement:
--   Take a finite train of source blocks with the occupied/vacuum patterns 10, 01, or 11, common phase, and occupied-pulse mean $x>0$ at Eve's ideal time-bin detector. In the specified intercept-resend construction, each occupied input is detected with probability $q=1-e^{-x}$; on detection a localized single photon is resent in that bin, otherwise vacuum is sent. A blocked bin remains vacuum. The resulting full-Fock density is the product of these diagonal localized-number mixtures.
--
--   For any two distinct occupied bins forming an illuminated tested pair, let $F_1,F_2$ denote the intrinsic mean output fluxes at their common interference slot of the balanced one-bin-delay monitor. Then the density is normalized, its required photon moments converge, and
--
--   $$
--   F_1=F_2={q\over2},\qquad F_1+F_2>0,\qquad V={F_1-F_2\over F_1+F_2}=0.
--   $$
--
--   This covers both within-decoy and 1,0-boundary tests, so both intrinsic visibilities in (21) vanish. It evaluates the localized resend construction; the distinct information-rate and exact count-preservation claims are deferred. Trusted dark counts are outside this intrinsic optical contrast.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 5, III.C.2, Fig.3 and (21)

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

/-- PDF p.5, Fig.3 and (21): construct the localized single-photon resend mixture
and evaluate its intrinsic monitor response on any illuminated tested pair.
Both within-decoy and cross-boundary pairs are covered. Trusted dark counts and
the unquantified first-order count-preservation assertion are separate. -/
theorem interceptResendMonitoring (n : ℕ) (w : Fin n → Fin 3) (x : ℝ) (hx : 0 < x) :
    IsDensity (interceptResend w x) ∧
    ∀ i j : Fin n × Bool, i ≠ j → sourceOccupation w i = 1 → sourceOccupation w j = 1 →
      FinitePairMoments (interceptResend w x) i j ∧
      monitorFlux (interceptResend w x) i j 0 = (1 - Real.exp (-x)) / 2 ∧
      monitorFlux (interceptResend w x) i j 1 = (1 - Real.exp (-x)) / 2 ∧
      0 < monitorFlux (interceptResend w x) i j 0 + monitorFlux (interceptResend w x) i j 1 ∧
      opticalVisibility (interceptResend w x) i j = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end

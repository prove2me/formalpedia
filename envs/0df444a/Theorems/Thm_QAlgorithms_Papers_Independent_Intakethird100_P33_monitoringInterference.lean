-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_monitoringInterference
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.monitoringInterference
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:49:20.686201+00:00
-- url     : https://prove2.me/theorems/32c79566-e4c6-454f-86cf-8e983c56f2d4
-- title:
--   II.C: coherent interference outputs and dark monitoring port
-- statement:
--   Let $\mu\ge0$ and $t,t_B\in[0,1]$, and put $x=\mu t(1-t_B)$ and $a=\sqrt{x}$. The two consecutive monitoring inputs have coherent amplitudes $b,c\in\{0,a\}$, with equal phase whenever both are occupied. The balanced one-bin-delay interferometer produces, at their common interference slot, normalized coherent output modes with amplitudes
--
--   $$
--   \beta_1=i(b+c)/2,\qquad\beta_2=(-b+c)/2.
--   $$
--
--   Port $r$ has mean photon number $|\beta_r|^2$ and ideal dark-count-free threshold-click probability $1-e^{-|\beta_r|^2}$. When $b=c=a$, the output is $|ia,0\rangle$, with mean intensities $x,0$ and zero click probability in the second port. This applies both within a decoy and across a 1,0 source-bit boundary. With exactly one occupied input, each selected-time output has mean intensity $x/4$ and the two click probabilities are equal. The all-vacuum case is included.
--
--   This is the optical coherence test; a nonempty input does not force a detection.
--
--   **Formalization Note** The source's single-input prose says $x/2$ per port. The displayed amplitude equations and endnote [6] instead give $x/4$, which is used here. Independent moderation of this disclosed correction remains required.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 2, II.C, (6)–(7)

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

/-- PDF p.2, (6)-(7), and p.7 endnote [6]: exact coherent interference.
Printed prose gives single-input intensity x/2; changed to x/4, as both the
amplitude equations and endnote [6] require. This correction needs independent
moderation. Equal-input DM2 is vacuum; no assertion forces DM1 to click. -/
theorem monitoringInterference (mu t tB : ℝ) (hmu : 0 ≤ mu)
    (ht : t ∈ Set.Icc 0 1) (htB : tB ∈ Set.Icc 0 1) :
    let x := mu * t * (1 - tB)
    let a : ℂ := Real.sqrt x
    (∀ u v : Bool,
      let b := if u then a else 0
      let c := if v then a else 0
      let out := monitoringOutput b c
      ‖out‖ = 1 ∧
      (∀ nm, out nm = coherentPairCoefficients
        (Complex.I * (b + c) / 2) ((-b + c) / 2) nm) ∧
      (∀ port : Fin 2, Summable (fun nm : ℕ × ℕ =>
        ((if port = 0 then nm.1 else nm.2 : ℕ) : ℝ) * Complex.normSq (out nm))) ∧
      photonMean out 0 = Complex.normSq (Complex.I * (b + c) / 2) ∧
      photonMean out 1 = Complex.normSq ((-b + c) / 2) ∧
      opticalClick out 0 = 1 - Real.exp (-Complex.normSq (Complex.I * (b + c) / 2)) ∧
      opticalClick out 1 = 1 - Real.exp (-Complex.normSq ((-b + c) / 2))) ∧
    monitoringOutput a a = coherentPair (Complex.I * a) 0 ∧
    photonMean (monitoringOutput a a) 0 = x ∧
    photonMean (monitoringOutput a a) 1 = 0 ∧
    opticalClick (monitoringOutput a a) 1 = 0 ∧
    (∀ out ∈ ({monitoringOutput a 0, monitoringOutput 0 a} : Set TwoModeFock),
      photonMean out 0 = x / 4 ∧ photonMean out 1 = x / 4 ∧
      opticalClick out 0 = opticalClick out 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end

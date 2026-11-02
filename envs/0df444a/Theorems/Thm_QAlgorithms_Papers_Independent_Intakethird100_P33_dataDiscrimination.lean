-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_dataDiscrimination
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.dataDiscrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:48:29.831194+00:00
-- url     : https://prove2.me/theorems/d823c6aa-9654-4b2b-83c3-c6376fe40763
-- title:
--   II.B: optimal unambiguous time-bin readout and absence of coding errors
-- statement:
--   Consider two orthogonal temporal modes, a perfect blocking switch, and a common zero optical phase. Let $\mu\ge0$ be the mean photon number in an occupied source pulse and let the channel transmission $t$, data-port transmission $t_B$, and trusted detector efficiency $\eta$ lie in $[0,1]$. After loss, put $x=\mu t t_B\eta$ and define the normalized full-Fock states $|0_x\rangle=|\sqrt{x},0\rangle$ and $|1_x\rangle=|0,\sqrt{x}\rangle$. The two nondecoy bits have equal conditional prior probabilities. Their overlap and optimal unambiguous discrimination probability are
--
--   $$
--   |\langle0_x|1_x\rangle|=e^{-x},\qquad p_{\rm success}=1-e^{-x}.
--   $$
--
--   Every three-outcome unambiguous POVM has average success probability at most this value. Photon counting attains it: a nonzero occupation exclusively in the early or late bin reports bit 0 or 1, respectively, while vacuum is inconclusive. Each state has inconclusive probability $e^{-x}$, and a wrong conclusive bit has probability zero. Optimality with $\eta<1$ concerns POVMs on the attenuated states. At $x=0$ the common state is vacuum and the optimal success is zero.
--
--   This gives the exact error-free data readout in the absence of dark counts; it does not assert a security rate.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 2, II.B, (4)–(5)

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

/-- PDF p.2, II.B and (4)-(5): exact optimal unambiguous readout on states AFTER
trusted efficiency loss, with equal bit priors and no dark counts. Includes an
attaining number-counting POVM, the universal bound, and absence of coding errors. -/
theorem dataDiscrimination (mu t tB eta : ℝ) (hmu : 0 ≤ mu)
    (ht : t ∈ Set.Icc 0 1) (htB : tB ∈ Set.Icc 0 1)
    (heta : eta ∈ Set.Icc 0 1) :
    let x := mu * t * tB * eta
    (∀ bit : Bool, ‖dataState x bit‖ = 1 ∧
      ∀ nm, dataState x bit nm =
        coherentPairCoefficients (if bit then 0 else (Real.sqrt x : ℂ))
          (if bit then (Real.sqrt x : ℂ) else 0) nm) ∧
    ‖inner ℂ (dataState x false) (dataState x true)‖ = Real.exp (-x) ∧
    (∃ M : OpticalPOVM (Fin 3),
      (∀ o nm pq, M.effect o nm pq =
        if nm = pq ∧ countingOutcome nm = o then 1 else 0) ∧
      Unambiguous M x ∧ discriminationSuccess M x = 1 - Real.exp (-x) ∧
      realFockTracePair (rankOne (dataState x false)) (M.effect 2) = Real.exp (-x) ∧
      realFockTracePair (rankOne (dataState x true)) (M.effect 2) = Real.exp (-x)) ∧
    (∀ M : OpticalPOVM (Fin 3), Unambiguous M x →
      discriminationSuccess M x ≤ 1 - Real.exp (-x)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_fockSubstitution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.fockSubstitution
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:50:02.423827+00:00
-- url     : https://prove2.me/theorems/6b815009-2ddb-4343-848c-58fbdfa4e8c0
-- title:
--   II.D: replacing nonempty coherent pulses by single photons makes distinct source sequences orthogonal
-- statement:
--   For $n\ge0$ two-bin source blocks, let $w\in\{0,1,d\}^n$ be a preparation word, where $d$ denotes a decoy. Replace every occupied coherent pulse by a one-photon Fock state and every blocked pulse by vacuum. The three block symbols then become $|1,0\rangle$, $|0,1\rangle$, and $|1,1\rangle$. Let $|F_w\rangle$ be their full multimode number-basis product. Then
--
--   $$
--   \|F_w\|=1,\qquad\langle F_w|F_v\rangle=\begin{cases}1,&w=v,\0,&w\ne v.\end{cases}
--   $$
--
--   For $n=0$, the sole empty word has norm one. This identifies the mathematical obstruction in the proposed direct Fock substitution, without claiming an impossibility theorem for other single-photon protocols.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 3, II.D, single-photon remark

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

/-- PDF p.3, II.D: replacing every occupied pulse by one photon gives orthogonal
number-basis words, including normalization of the unique zero-block word. -/
theorem fockSubstitution (n : ℕ) :
    (∀ w : Fin n → Fin 3, ‖substitutedWord w‖ = 1) ∧
    (∀ w v : Fin n → Fin 3,
      inner ℂ (substitutedWord w) (substitutedWord v) = if w = v then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_characteristicAction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.characteristicAction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:20:36.732286+00:00
-- url     : https://prove2.me/theorems/8429f3c4-2412-4633-a9b4-1e84e8fa1c6f
-- title:
--   Receiver and weak-complement characteristic-function laws
-- statement:
--   Let $k\ge0$ and let a bounded two-mode unitary $U$ implement exactly matrix (11) for $k\le1$ or matrix (12) for $k\ge1$. Fix a centered, possibly mixed Gaussian environmental density $\sigma$. For any input density $\rho$, write $\chi(z)=\operatorname{Tr}(\rho D(z))$ and $\xi(z)=\operatorname{Tr}(\sigma D(z))$, where $D(z)=\exp(za^\dagger-\overline z a)$. The receiver $E$ and weak complement $F$ obtained from this same dilation are full trace-class CPTP maps. For every complex $z$,
--
--   $$
--   \begin{array}{ll}
--   0\le k\le1:&\chi_{E(\rho)}(z)=\chi(\sqrt k z)\xi(\sqrt{1-k}z),\\
--   &\chi_{F(\rho)}(z)=\chi(-\sqrt{1-k}z)\xi(\sqrt k z);\\[2pt]
--   k\ge1:&\chi_{E(\rho)}(z)=\chi(\sqrt k z)\xi(-\sqrt{k-1}\,\overline z),\\
--   &\chi_{F(\rho)}(z)=\chi(-\sqrt{k-1}\,\overline z)\xi(\sqrt k z).
--   \end{array}
--   $$
--
--   The formulas describe arbitrary inputs on the complete Fock space and agree at $k=1$.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 4, §IV, (15)-(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section IV, (15),(17), PDF p.4: BOTH output weylCharacteristic functions for
EVERY input density, with the same centered Gaussian environment. The maps are
constructed by (1),(2), not by assuming these weylCharacteristic-function laws. -/
theorem characteristicAction (k : ℝ) (hk : 0 ≤ k)
    (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (hcanonical : Canonical U (standardMatrix k))
    (sigma : State ℕ) (hcentered : CenteredGaussian sigma.coefficients) :
    IsTraceClassChannel (dilationReceiver U sigma.coefficients) ∧
    IsTraceClassChannel (weakComplement U sigma.coefficients) ∧
    ∀ (rho : State ℕ) (z : ℂ),
      (k ≤ 1 →
        weylCharacteristic (dilationReceiver U sigma.coefficients rho.coefficients) z =
          weylCharacteristic rho.coefficients ((Real.sqrt k : ℂ) * z) *
            weylCharacteristic sigma.coefficients ((Real.sqrt (1 - k) : ℂ) * z) ∧
        weylCharacteristic (weakComplement U sigma.coefficients rho.coefficients) z =
          weylCharacteristic rho.coefficients (-(Real.sqrt (1 - k) : ℂ) * z) *
            weylCharacteristic sigma.coefficients ((Real.sqrt k : ℂ) * z)) ∧
      (1 ≤ k →
        weylCharacteristic (dilationReceiver U sigma.coefficients rho.coefficients) z =
          weylCharacteristic rho.coefficients ((Real.sqrt k : ℂ) * z) *
            weylCharacteristic sigma.coefficients (-(Real.sqrt (k - 1) : ℂ) * star z) ∧
        weylCharacteristic (weakComplement U sigma.coefficients rho.coefficients) z =
          weylCharacteristic rho.coefficients (-(Real.sqrt (k - 1) : ℂ) * star z) *
            weylCharacteristic sigma.coefficients ((Real.sqrt k : ℂ) * z)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end

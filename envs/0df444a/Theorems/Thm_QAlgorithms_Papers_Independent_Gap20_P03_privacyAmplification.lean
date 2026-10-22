-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_privacyAmplification
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.privacyAmplification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:18:43.017248+00:00
-- url     : https://prove2.me/theorems/8eb78434-287a-4d83-8a64-fc1d1067c166
-- title:
--   Theorem 4.1: privacy amplification with classical conditioning
-- statement:
--   Let $\rho_{XUE}$ be a normalized ccq-state, where $X\in\{0,1\}^n$, $U$ has a finite alphabet, and $E$ consists of $q$ qubits. Let $F$ be uniform in a finite nonempty two-universal family of maps to $\{0,1\}^\ell$, independent of the entire original state. For $\varepsilon\ge0$,
--   $$\delta\!\left(\rho_{F(X)FUE},2^{-\ell}I\otimes\rho_{FUE}\right)\le\tfrac12\,2^{-[H_\infty^\varepsilon(X\mid U)-q-\ell]/2}+2\varepsilon.$$
--   Here $\delta$ is half the trace norm, and $H_\infty^\varepsilon$ is the classical worst-case event-smoothed entropy with the original conditioning denominator. At infinite entropy the exponential is interpreted by its extended limit. This extracts a key while accounting separately for classical information and stored quantum qubits.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 8, Theorem 4.1: privacy amplification with classical conditioning

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Theorem 4.1, p.8, privacy amplification with CLASSICAL conditioning.
Trace distance is HALF trace norm; q and ell are both inside the exponent.
The ENNReal right-hand side preserves the all-deleted epsilon≥1 convention. -/
theorem privacyAmplification {K U : Type*} [Fintype K] [Nonempty K]
    [Fintype U] [Nonempty U] (n ell q : ℕ)
    (hash : K → Qubits n → Qubits ell) (hhash : TwoUniversal hash)
    (blocks : (Qubits n × U) → Matrix (Qubits q) (Qubits q) ℂ)
    (hblocks : IsNormalizedCQBlocks blocks) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ENNReal.ofReal (traceDistance (cqBlockOperator (hashedBlocks hash blocks))
      (cqBlockOperator (uniformFirst (hashedBlocks hash blocks)))) ≤
    ENNReal.ofReal ((1/2:ℝ) * Real.rpow 2 (((q:ℝ)+ell)/2)) *
      entropyFactor (smoothMin (fun a => ENNReal.ofReal ((blocks a).trace.re))
        Prod.fst Prod.snd epsilon) + ENNReal.ofReal (2*epsilon) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end

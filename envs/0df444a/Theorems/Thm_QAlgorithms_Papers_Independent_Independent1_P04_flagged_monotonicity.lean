-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_flagged_monotonicity
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.flagged_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:24:18.200039+00:00
-- url     : https://prove2.me/theorems/7eafac54-be6f-4ec6-8d13-22c9fcc4f55e
-- title:
--   Monotonicity with a classical flag
-- statement:
--   Let $\rho$ be a density matrix and let $K_a$ be a complete incoherent Kraus family with common positive output dimension $e$. Put the flag first in its classical basis and define the unnormalized-block sum
--   $$\omega=\sum_a|a\rangle\langle a|\otimes K_a\rho K_a^\dagger.$$
--   Then $\omega$ is a density matrix, $C_{\rm rel}(\omega)\le C_{\rm rel}(\rho)$ and $C_1(\omega)\le C_1(\rho)$. The product basis is flattened consistently to dimension $ae$. Zero-probability blocks contribute zero without division.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix D (C2c), (D.1)–(D.4), PDF p. 8. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq





























































/-- PDF pp.7–8, (C2c), (D.1)–(D.4): flagged monotonicity of the two concrete measures. -/
theorem flagged_monotonicity (d e a : ℕ) (hd : 0 < d) (he : 0 < e)
    (K : Fin a → Matrix (Fin e) (Fin d) ℂ) (hK : IncoherentInstrument (fun _ => e) K)
    (rho : CoherenceMatrix d) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (flaggedOutput K rho) ∧
    entropyCoherence (a*e) (flaggedOutput K rho) ≤ entropyCoherence d rho ∧
    Coherence.l1Coherence (flaggedOutput K rho) ≤ Coherence.l1Coherence rho := by sorry





end QAlgorithms.Papers.Independent.Independent1.P04

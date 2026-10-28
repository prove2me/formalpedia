-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_relative_entropy_maximum
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_maximum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:27.064855+00:00
-- url     : https://prove2.me/theorems/7e365ca9-bf27-4675-b9c9-4bdf29c3f639
-- title:
--   Relative-entropy maximum
-- statement:
--   For every density matrix $\rho$ in dimension $d\ge1$, natural-log entropy gives
--   $$C_{\rm rel}(\rho)\le S(\Delta\rho)\le\log d.$$
--   The vector $|\Psi_d\rangle=d^{-1/2}\sum_i|i\rangle$ is normalized and satisfies $C_{\rm rel}(|\Psi_d\rangle\langle\Psi_d|)=\log d$. This identifies an attaining witness without a uniqueness claim. Dimension one yields zero.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Following Eq.(8), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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

























































/-- PDF p.3 after (8): both entropy bounds and their attainment by (4), including d=1. -/
theorem relative_entropy_maximum (d : ℕ) (hd : 0 < d) :
    (∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      entropyCoherence d rho ≤ naturalEntropy (dephasedMatrix rho) ∧
        naturalEntropy (dephasedMatrix rho) ≤ Real.log d) ∧
    IsState (uniformCoherentVector d) ∧
    entropyCoherence d (pureDensity (uniformCoherentVector d)) = Real.log d := by sorry









end QAlgorithms.Papers.Independent.Independent1.P04

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_squared_l2_minimum
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.squared_l2_minimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:43.353983+00:00
-- url     : https://prove2.me/theorems/85c45998-1210-46f0-9797-ef90a10f7bbf
-- title:
--   Squared Hilbert–Schmidt incoherent minimum
-- statement:
--   For a density matrix $\rho$ in any dimension $d\ge1$, the diagonal density matrix $\Delta\rho$ attains
--   $$\min_{\delta\ {\rm diagonal}}\sum_{i,j}|\rho_{ij}-\delta_{ij}|^2=\sum_{i\ne j}|\rho_{ij}|^2.$$
--   The theorem includes the minimizing value and its comparison with every incoherent density matrix. This is the squared Hilbert–Schmidt distance, not the operator norm; it does not assert coherence monotonicity.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Eq.(10), Appendix G (G.1), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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




























































/-- PDF pp.3,10, (10), (G.1): squared Hilbert–Schmidt minimum; both off-diagonal orders count. -/
theorem squared_l2_minimum (d : ℕ) (hd : 0 < d) (rho : CoherenceMatrix d)
    (hrho : IsDensityMatrix rho) :
    IncoherentState (dephasedMatrix rho) ∧
    squaredHSDistance rho (dephasedMatrix rho) = squaredOffDiagonal rho ∧
    distanceCandidate squaredHSDistance rho = squaredOffDiagonal rho ∧
    ∀ delta, IncoherentState delta → squaredOffDiagonal rho ≤ squaredHSDistance rho delta := by sorry






end QAlgorithms.Papers.Independent.Independent1.P04

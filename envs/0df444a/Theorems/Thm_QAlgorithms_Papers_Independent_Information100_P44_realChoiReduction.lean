-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_realChoiReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P44.realChoiReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:47:34.184503+00:00
-- url     : https://prove2.me/theorems/f725f3e0-60bd-4171-8489-79f5284f06f7
-- title:
--   V E: real-part reduction preserves feasibility and objectives
-- statement:
--   For the fixed four-level SDP, let $J$ be any feasible complex Choi matrix and let $A$ be its entrywise real part, regarded again as a complex matrix: $A_{pq}=\operatorname{Re}J_{pq}$. Then
--   $$A\text{ is feasible},\qquad L_k(A)=L_k(J)\quad(k\in\{01a,1b3,03\}).$$
--   The operation is entrywise real part, not Hermitian symmetrization. It permits the three optimization problems to be restricted to real symmetric matrices.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 18, V E: real-part reduction preserves feasibility and objectives

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.18, Eq.(134): entrywise real part, not the Hermitian part of J. -/
theorem realChoiReduction (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hJ : FixedChoiFeasible J) :
    FixedChoiFeasible (fun a b => ((J a b).re : ℂ)) ∧
    ∀ k : Fin 3, channelObjective k (fromChoi (fun a b => ((J a b).re : ℂ))) = channelObjective k (fromChoi J) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44

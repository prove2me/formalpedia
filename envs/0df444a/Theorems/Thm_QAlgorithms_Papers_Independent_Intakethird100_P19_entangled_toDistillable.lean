-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_entangled_toDistillable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.entangled_toDistillable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:39:19.993792+00:00
-- url     : https://prove2.me/theorems/7c38eae6-d623-4e06-b24f-67be9750c5e5
-- title:
--   Theorem 13: entangled inputs reach LOCC-distillable states
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. LOCC-distillable means that channels $\Lambda_n$ obtainable by local operations and classical communication satisfy $\|\Lambda_n(\rho^{\otimes n})-\phi_2^+\|_1\to0$, with copies regrouped by party. For each entangled bipartite state $\rho$, there is a dually non-entangling channel $\Lambda$ to two qubits for which
--
--   $$\Lambda(\rho)\text{ is LOCC-distillable}.$$
--
--   This is a single-copy conversion to a distillable state.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 17, Theorem 13

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 13, PDF p.17: every entangled state, including PPT-entangled
states, has a single-copy conversion to a two-qubit LOCC-distillable state. -/
theorem entangled_toDistillable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Bip a b) (hrho : IsDensityMatrix rho) (hent : ¬ IsSeparablePositive rho) :
    ∃ L : Superop (Fin a × Fin b) (Fin 2 × Fin 2),
      IsChannel L ∧ DNE L ∧ LOCCDistillable (L rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end

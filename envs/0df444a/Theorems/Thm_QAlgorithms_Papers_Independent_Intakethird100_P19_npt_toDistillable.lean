-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_npt_toDistillable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.npt_toDistillable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:39:50.898059+00:00
-- url     : https://prove2.me/theorems/2c45a459-0869-47cb-95f4-d17e7b04c7ed
-- title:
--   Theorem 14: NPT conversion by PPT and dually non-entangling channels
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. LOCC-distillable means that channels $\Lambda_n$ obtainable by local operations and classical communication satisfy $\|\Lambda_n(\rho^{\otimes n})-\phi_2^+\|_1\to0$, with copies regrouped by party. For every state $\rho$ with $\rho^\Gamma\not\ge0$, there exists a channel $\Lambda$ to two qubits such that
--
--   $$\Lambda\text{ is dually non-entangling},\quad J(\Lambda)\text{ is PPT across }A_{\rm out}A_{\rm in}:B_{\rm out}B_{\rm in},\quad\Lambda(\rho)\text{ is LOCC-distillable}.$$
--
--   This is the strengthened NPT conversion advertised in the abstract.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 17, Theorem 14

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

/-- Theorem 14, PDF p.17 (abstract headline p.1): a single-copy NPT input
is converted to a two-qubit LOCC-distillable state by a channel which is both
dually non-entangling and PPT in its grouped Choi representation. -/
theorem npt_toDistillable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Bip a b) (hrho : IsDensityMatrix rho)
    (hnpt : ¬ (partialTransposeFirst rho).PosSemidef) :
    ∃ L : Superop (Fin a × Fin b) (Fin 2 × Fin 2),
      IsChannel L ∧ DNE L ∧ ChoiPPT L ∧ LOCCDistillable (L rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end

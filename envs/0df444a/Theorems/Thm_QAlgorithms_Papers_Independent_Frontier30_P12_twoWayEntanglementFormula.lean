-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_twoWayEntanglementFormula
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.twoWayEntanglementFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:13:27.960217+00:00
-- url     : https://prove2.me/theorems/4c4bbf76-7cb5-4fb8-be2b-40eba78dd69a
-- title:
--   Theorem 15: regularized two-way entanglement capacity
-- statement:
--   Let $\rho^{AB}$ be a normalized density matrix on finite complex registers of dimensions $a,b\ge1$. Let $D(\rho)$ be its operational two-way EPR distillation capacity, defined as the supremum of rates attained by genuine finite LOCC protocols on $n$ independent copies, with no additional shared state, EPR squared fidelity tending to one, and $\log_2M_n/n$ converging for protocols defined for every $n$. Then
--
--   $$D(\rho)=\lim_{n\to\infty}\frac1n\sup_V I_c(A'\rangle B')_{V(\rho^{\otimes n})}.$$
--
--   Here $I_c(A'\rangle B')=H(B')-H(A'B')$ in bits. The supremum permits arbitrary finite positive output dimensions, dimension-changing local Kraus instruments, local ancillas and disposal, and any finite number of adaptive classical communication rounds. Taking the supremum includes limiting approximation by finite protocols; no optimal LOCC map is asserted to exist.
--
--   The limit's existence is part of the conclusion. The source credits [33] for these consequences of hashing and supplies this theorem's argument on p.10.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 10, Theorem 15

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.10, Theorem 15; Section IV credits [33]
for the consequence of hashing. The supremum is over actual finite LOCC maps,
including arbitrary finite output dimensions and limiting approximation.
The existence of the displayed limit is part of the conclusion. -/
theorem twoWayEntanglementFormula {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (h : QAlgorithms.IsDensityMatrix rho) :
    Tendsto (fun n => twoWaySingle rho n / n) atTop (nhds (twoWayCapacity rho)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end

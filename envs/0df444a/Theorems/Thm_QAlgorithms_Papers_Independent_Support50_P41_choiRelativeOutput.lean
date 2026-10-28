-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_choiRelativeOutput
-- name    : QAlgorithms.Papers.Independent.Support50.P41.choiRelativeOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:33:28.867701+00:00
-- url     : https://prove2.me/theorems/c1abd60a-cec7-455c-b15b-3b2370ab8eee
-- title:
--   §A.2: channel outputs recovered by contracting the Choi operator
-- statement:
--   Let $\Phi$ be a complex-linear CPTP map on dimension $d\ge1$, and let $v$ be a unit vector. Form the unnormalized input-first Choi operator $D=(\mathrm{id}\otimes\Phi)(|\widetilde\Omega\rangle\langle\widetilde\Omega|)$, where $\widetilde\Omega=\sum_i|i,i\rangle$. If $v^*=\bar v$ in the paired reference basis, then
--
--   $$\Phi(|v\rangle\langle v|)=(\langle v^*|\otimes I)D(|v^*\rangle\otimes I).$$
--
--   This recovers channel output from the Choi operator without a missing factor of $d$.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 33, §A.2: channel outputs recovered by contracting the Choi operator

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.32--33: pure-state output by contraction of the unnormalized input-first Choi operator. -/
theorem choiRelativeOutput {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    Phi (pureDensity v) = relativeOperator (indexState v) (choi Phi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

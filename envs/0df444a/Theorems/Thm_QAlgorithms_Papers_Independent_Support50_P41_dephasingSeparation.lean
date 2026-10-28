-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_dephasingSeparation
-- name    : QAlgorithms.Papers.Independent.Support50.P41.dephasingSeparation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:18:34.871162+00:00
-- url     : https://prove2.me/theorems/941fa2e5-dde4-48c2-a6b1-b595bb6e6edd
-- title:
--   §4.3: dephasing separates state and entanglement fidelity
-- statement:
--   Let $p_i\ge0$ sum to one, with at least two positive entries, and put $\rho=\operatorname{diag}(p_i)$. Let $\Delta$ be complete dephasing in that same basis, and $\psi$ any normalized purification. Then
--
--   $$\Delta(\rho)=\rho,\qquad F(\rho,\Delta(\rho))=1,\qquad F_e(\psi,\Delta)=\sum_i p_i^2<1.$$
--
--   This explicit example separates squared state fidelity from entanglement fidelity.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 16, §4.3: dephasing separates state and entanglement fidelity

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

/-- PDF p.16: dephasing fixes diagonal inputs but lowers entanglement fidelity for mixed inputs. -/
theorem dephasingSeparation {d a : ℕ} [NeZero d] (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1)
    (hmixed : ∃ i j, i ≠ j ∧ 0 < p i ∧ 0 < p j)
    (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (hpsi : IsPurification (Matrix.diagonal fun i => (p i : ℂ)) psi) :
    let rho := Matrix.diagonal fun i => (p i : ℂ)
    dephasing rho = rho ∧ rootFidelity rho (dephasing rho)^2 = 1 ∧
      purificationFidelity psi dephasing = ∑ i, (p i)^2 ∧
      purificationFidelity psi dephasing < 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

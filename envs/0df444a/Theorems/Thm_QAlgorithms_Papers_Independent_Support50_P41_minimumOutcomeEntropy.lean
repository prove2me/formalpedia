-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_minimumOutcomeEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.minimumOutcomeEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:22:38.637597+00:00
-- url     : https://prove2.me/theorems/886e38fe-131f-44f4-b7f0-b57178d817d2
-- title:
--   §5.1, equation (15): attained minimum over Kraus representations
-- statement:
--   For a density matrix $\rho$ and CPTP map $\Phi$ on a nonzero finite-dimensional system, every countably indexed normalized operator-sum representation $(A_k)$ gives probabilities $P_k=\operatorname{Tr}(A_k\rho A_k^\dagger)$ satisfying
--
--   $$S_e(\rho,\Phi)\le H(P):=-\sum_k P_k\log_2P_k.$$
--
--   The Shannon entropy may be infinite. Some finite Kraus representation attains equality, so the bound is an attained minimum over representations. The minimizing representation may depend on $\rho$.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 21, §5.1, equation (15): attained minimum over Kraus representations

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

/-- PDF p.21, (15): lower bound for all countable Kraus representations and an attaining finite representation; no infimum default. -/
theorem minimumOutcomeEntropy {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ (K : Type) [Countable K] (A : K → Matrix (Fin d) (Fin d) ℂ),
      CountableOperatorSum Phi A →
      ENNReal.ofReal (entropyExchange Phi rho) ≤
        countableEntropy (fun k => (A k * rho * (A k)ᴴ).trace.re)) ∧
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ entropyExchange Phi rho = outcomeEntropy A rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

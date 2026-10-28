-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_krausEnsembleCorrespondence
-- name    : QAlgorithms.Papers.Independent.Support50.P41.krausEnsembleCorrespondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:35:18.873216+00:00
-- url     : https://prove2.me/theorems/780c2f34-0c7d-434f-83b7-a16c3a6ef21c
-- title:
--   §A.4: Kraus representations and Choi-state vector ensembles
-- statement:
--   Fix a complex-linear CPTP map $\Phi$ on dimension $d\ge1$ and a countable label set $K$, including any finite set. Let $D$ be its unnormalized input-first Choi operator. The coordinate map from a matrix family $(A_k)$ to $v_k=\operatorname{vec}(A_k)/\sqrt d$ is bijective, and
--
--   $$\sum_k A_k^\dagger A_k=I,\quad \Phi(X)=\sum_k A_kXA_k^\dagger\ \text{for every }X
--   \quad\Longleftrightarrow\quad \sum_k|v_k\rangle\langle v_k|=D/d.$$
--
--   All series are convergent operator sums. This is a correspondence of indexed subnormalized vectors, preserving phases and zero entries, rather than unordered ensembles of rays.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 36, §A.4: Kraus representations and Choi-state vector ensembles

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

/-- PDF pp.33--34,36: indexed subnormalized-vector ensembles of D/d correspond bijectively to Kraus lists. -/
theorem krausEnsembleCorrespondence {K : Type*} [Countable K] {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    Function.Bijective (fun A : K → Matrix (Fin d) (Fin d) ℂ =>
      fun k => normalizedOperatorVector (A k)) ∧
    ∀ A : K → Matrix (Fin d) (Fin d) ℂ,
      CountableOperatorSum Phi A ↔
      HasSum (fun k => pureDensity (normalizedOperatorVector (A k)))
        (((d : ℂ)⁻¹) • choi Phi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

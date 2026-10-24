-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_dilationPurifications
-- name    : QAlgorithms.Papers.Independent.Support50.P41.dilationPurifications
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:35:59.611214+00:00
-- url     : https://prove2.me/theorems/56c5a882-81f8-4942-b511-dcaac992540c
-- title:
--   §A.4: unitary representations and purifications of the channel state
-- statement:
--   Let $\Phi$ be a complex-linear CPTP map on dimension $d\ge1$, $D$ its unnormalized input-first Choi operator, and $E$ a nonzero finite environment. Applying any pure-environment unitary representation to normalized $\Omega_{RQ}$ produces a unit vector $v$ with
--
--   $$\operatorname{Tr}_E|v\rangle\langle v|=D/d.$$
--
--   Conversely, every such normalized purification $v$ and every unit initial environment vector $\eta$ admit a unitary representation whose output on $\Omega_{RQ}\otimes\eta$ is exactly $v$. This supplies both constructions; the full unitary need not be unique on the unused orthogonal complement.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 36, §A.4: unitary representations and purifications of the channel state

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

/-- PDF pp.35--36: both constructions between dilations and channel-state purifications, without full-unitary bijectivity. -/
theorem dilationPurifications {d e : ℕ} [NeZero d] [NeZero e]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    (∀ (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)),
      IsState eta → (∀ X, Phi X = dilationChannel U eta X) →
      IsState (dilationChoiVector U eta) ∧
        traceRight (pureDensity (dilationChoiVector U eta)) = ((d : ℂ)⁻¹) • choi Phi) ∧
    (∀ (v : EuclideanSpace ℂ ((Fin d × Fin d) × Fin e)), IsState v →
      traceRight (pureDensity v) = ((d : ℂ)⁻¹) • choi Phi →
      ∀ eta : EuclideanSpace ℂ (Fin e), IsState eta →
        ∃ U : Matrix.unitaryGroup (Fin d × Fin e) ℂ,
          (∀ X, Phi X = dilationChannel U eta X) ∧ dilationChoiVector U eta = v) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

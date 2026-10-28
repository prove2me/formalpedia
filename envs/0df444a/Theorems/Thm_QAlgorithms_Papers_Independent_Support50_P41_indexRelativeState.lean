-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_indexRelativeState
-- name    : QAlgorithms.Papers.Independent.Support50.P41.indexRelativeState
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:32:38.451772+00:00
-- url     : https://prove2.me/theorems/c9c0cc4c-aff1-48b6-a852-848184d1082d
-- title:
--   §A.1: conjugate-linear index and relative-state correspondence
-- statement:
--   In paired orthonormal bases of two $d$-dimensional spaces, $d\ge1$, let $Jv=\bar v$ and $\widetilde\Omega=\sum_i|i\rangle_R|i\rangle_Q$. Then
--
--   $$J^2v=v,\quad \langle Jv|\widetilde\Omega\rangle=v,\quad
--   \langle Jv|\Omega\rangle=v/\sqrt d,\quad \|\widetilde\Omega\|^2=d,$$
--
--   where $\Omega=\widetilde\Omega/\sqrt d$. The map $J$ is conjugate linear. For unit $v$, writing $P=|Jv\rangle\langle Jv|\otimes I$, also $|Jv\rangle\langle Jv|\otimes|v\rangle\langle v|=P|\widetilde\Omega\rangle\langle\widetilde\Omega|P$. This identifies index states and relative states with the source normalization.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 31, §A.1: conjugate-linear index and relative-state correspondence

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

/-- PDF pp.31--32: inverse conjugate-linear index correspondence, normalization and unit-vector projector identity. -/
theorem indexRelativeState {d : ℕ} [NeZero d] :
    (∀ v : EuclideanSpace ℂ (Fin d), indexState (indexState v) = v ∧
      relativeVector (indexState v) (omegaTilde d) = v ∧
      relativeVector (indexState v) (finiteMaxEntangled (Fin d)) = ((Real.sqrt d)⁻¹ : ℂ) • v) ∧
    (∀ (v w : EuclideanSpace ℂ (Fin d)) (z t : ℂ),
      indexState (z • v + t • w) = conj z • indexState v + conj t • indexState w) ∧
    (∀ v : EuclideanSpace ℂ (Fin d), IsState v →
      Matrix.kronecker (pureDensity (indexState v)) (pureDensity v) =
        conjSuperop (Matrix.kronecker (pureDensity (indexState v))
          (1 : Matrix (Fin d) (Fin d) ℂ)) (pureDensity (omegaTilde d))) ∧
    ‖omegaTilde d‖^2 = (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end

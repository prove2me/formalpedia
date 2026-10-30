-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_optimal_measurement
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.optimal_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:10:39.005124+00:00
-- url     : https://prove2.me/theorems/0b1b5336-6901-4557-a11e-7017ef4d22a6
-- title:
--   Lemma A.4: optimal POVM, classical subsystem clause
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on a finite-dimensional system $Z\otimes B$. For any discrete POVM $\{\Gamma_x\}$, put $P(x)=\operatorname{tr}(\Gamma_x\rho)$ and $Q(x)=\operatorname{tr}(\Gamma_x\sigma)$. Then
--
--   $$D(P,Q)\le D(\rho,\sigma),\qquad \exists\text{ a binary POVM with }D(P,Q)=D(\rho,\sigma).$$
--
--   If both states are classical in the designated basis of $Z$, an attaining POVM can be chosen with
--
--   $$\Gamma_x=\sum_z |z\rangle\langle z|\otimes M_{xz}.$$
--
--   Thus an optimal measurement can preserve the classical subsystem. The statement asserts existence of a preserving optimum, rather than a property of every optimum. Discrete POVM sums converge to the identity; the classical blocks of the states retain their respective weights.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 38, Lemma A.4: optimal POVM, classical subsystem clause

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.38, Lemma A.4: all discrete POVMs contract trace distance; a binary
POVM attains the maximum. With a classical first register an optimal POVM
has the block form of Eq.(23); only existence of such an optimum is asserted. -/
theorem optimal_measurement {Z B : Type} [Fintype Z] [Fintype B]
    [DecidableEq Z] [DecidableEq B]
    (rho sigma : Matrix (Z × B) (Z × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ (O : Type) (M : O → Matrix (Z × B) (Z × B) ℂ), IsDiscretePOVM M →
      discreteTV (fun o => effectProb (M o) rho) (fun o => effectProb (M o) sigma) ≤
        traceDistance rho sigma) ∧
    (∃ M : Bool → Matrix (Z × B) (Z × B) ℂ, IsPOVM M ∧
      discreteTV (fun o => effectProb (M o) rho) (fun o => effectProb (M o) sigma) =
        traceDistance rho sigma) ∧
    (ClassicalFirst rho → ClassicalFirst sigma →
      ∃ (M : Bool → Matrix (Z × B) (Z × B) ℂ) (blocks : Bool → Z → Matrix B B ℂ),
        IsPOVM M ∧
        discreteTV (fun o => effectProb (M o) rho) (fun o => effectProb (M o) sigma) =
          traceDistance rho sigma ∧
        ∀ o z zprime b bprime,
          M o (z,b) (zprime,bprime) = if z = zprime then blocks o z b bprime else 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end

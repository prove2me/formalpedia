-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_strongSubadditivityRecovery
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.strongSubadditivityRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:12:14.044558+00:00
-- url     : https://prove2.me/theorems/74404a89-cfa3-4484-8873-033510478b71
-- title:
--   Universal recovery refinement of strong subadditivity
-- statement:
--   Let A,B,C be finite-dimensional complex Hilbert spaces and let ρABC be a density operator. Write ρAB and ρBC for its marginals and I(A:C|B)ρ=H(AB)ρ+H(BC)ρ−H(ABC)ρ−H(B)ρ, with entropy in nats. Define the map R:B→BC from σ=ρBC and N=trC by (21): R=∫β₀(t)Rᵗ⁄²σ,N dt, with support-zero powers and the Petz map of (5). This map depends only on ρBC. Then
--
--   $$I(A:C\mid B)_\rho\ge-2\log F\!\left(\rho_{ABC},(\operatorname{id}_A\otimes\mathcal R)(\rho_{AB})\right).$$
--
--   Here F is root fidelity, and −log(0)=+∞. The recovery operation acts on B while preserving the spectator A.
--
--   **Source correction.** The average uses t/2 from (21), following the preceding application of Remark 2.2; the final line on p.16 instead prints t.
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 16, Corollary 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Corollary 4.1, PDF p.16, Eq.(101). SOURCE CORRECTION: the printed R^t average
is replaced by Eq.(21)'s R^(t/2), as required by the preceding derivation from Remark 2.2.
The identity on the spectator system A is explicit. -/
theorem strongSubadditivityRecovery {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (rho : Mat (I × (J × K))) (hrho : IsDensityMatrix rho) :
    fidelityPenalty (rootFidelity rho
      (idTensorSuperop (R := I) (recovery (traceLeft rho) (traceRight (α := J) (β := K)))
        (marginalAB rho))) ≤ (conditionalMutualInfo rho : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end

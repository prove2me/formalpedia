-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_tensor_local_duality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.tensor_local_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:27:11.077839+00:00
-- url     : https://prove2.me/theorems/948aaf5d-4218-4a21-be88-10a528bca04c
-- title:
--   Tensor-product local recovery duality
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Here $F$ denotes either root entanglement fidelity $F_\rho$ for any normalized input density $\rho$, with an identity reference retained, or worst-case root entanglement fidelity $F_W$ over all normalized logical densities for an arbitrary isometry $W$. Let $\mathcal N_A$ be a channel on $H_A$ and let $\widehat{\mathcal N_A}$ be any complementary channel to an environment $E$. The comparison domain is the joint system $H_A\otimes H_B$; a code may be entangled across the factors. Put $\mathcal D_\sigma(X)=\sigma\operatorname{Tr}X$. Both maxima are attained and
--
--   $$
--   \max_{\mathcal R_A}F((\mathcal R_A\mathcal N_A)\otimes\mathrm{id}_B,\mathrm{id}_{AB})=\max_{\sigma\succeq0,\,\operatorname{Tr}\sigma=1}F(\widehat{\mathcal N_A}\otimes\mathrm{id}_B,\mathcal D_\sigma\otimes\mathrm{id}_B).
--   $$
--
--   The recovery acts only on $A$. This independently stated tensor specialization retains arbitrary joint encodings.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 9, §IV D, Eq.(48): tensor-product local recovery duality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P44

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P48 (operatorTraceDual)

open QAlgorithms.Papers.Independent.Renew46.P43 (purification)

variable {H K L J E F B : Type*}

variable [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype B] [DecidableEq B]

/-- PDF p.9, Eq.(48), for either fidelity, including joint entangled codes. -/
theorem tensor_local_duality [Nonempty H] [Nonempty B] [Nonempty E]
    (N : Superop H H) (hN : IsChannel N) (CN : Superop H E)
    (hCN : IsGeneralizedComplement N CN) (c : Comparison (H × B)) :
    SameMaximum (fun R : Superop H H => IsChannel R)
      (fun R => comparisonRootFidelity c (mapFirst (R ∘ N)) (id : Superop (H × B) (H × B)))
      (fun sigma : Mat E => IsDensityMatrix sigma)
      (fun sigma => comparisonRootFidelity c (mapFirst CN)
        (mapFirst (constantChannel (H := H) sigma))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end

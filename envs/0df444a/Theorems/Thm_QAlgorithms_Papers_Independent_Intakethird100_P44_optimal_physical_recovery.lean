-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_optimal_physical_recovery
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.optimal_physical_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:21:05.895962+00:00
-- url     : https://prove2.me/theorems/6034736f-6c2e-44e5-8378-5c93c71b189c
-- title:
--   Optimal physical recovery duality
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Here $F$ denotes either root entanglement fidelity $F_\rho$ for any normalized input density $\rho$, with an identity reference retained, or worst-case root entanglement fidelity $F_W$ over all normalized logical densities for an arbitrary isometry $W$. Let $\mathcal P$ and $\mathcal Q$ be canonical Hilbert–Schmidt projections onto the input and output physical dagger algebras. Suppose $\mathcal N$ is physical, $\mathcal Q\mathcal N\mathcal P=\mathcal Q\mathcal N$, and let $\mathcal M$ be any channel from the input space to itself. Choose any complementary channels of the composite maps $\mathcal Q\mathcal N$ and $\mathcal P\mathcal M$, including complements equivalent by CPTP postprocessing in both directions. Then the attained maxima satisfy
--
--   $$
--   \max_{\mathcal P\mathcal R\mathcal Q=\mathcal P\mathcal R}F(\mathcal R\mathcal N,\mathcal P\mathcal M)=\max_{\mathcal S}F(\widehat{\mathcal Q\mathcal N},\mathcal S\widehat{\mathcal P\mathcal M}).
--   $$
--
--   All optimizers are CPTP, and the dual optimizer is unconstrained. This characterizes physical recovery without assuming $\mathcal M=\mathcal P\mathcal M$.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 5, Corollary 5, Eq.(13): optimal physical recovery

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

/-- PDF p.5, Corollary 5, Eq.(13). The hats cover QN and PM, respectively.
M is arbitrary; it is NOT required to satisfy M=PM. -/
theorem optimal_physical_recovery [Nonempty H] [Nonempty K]
    [Nonempty E] [Nonempty F]
    (P : ObservableAlgebra H) (Q : ObservableAlgebra K)
    (N : Superop H K) (M : Superop H H) (hN : IsChannel N) (hM : IsChannel M)
    (hphys : IsPhysicalChannel P.project Q.project N)
    (CN : Superop H E) (CM : Superop H F)
    (hCN : IsGeneralizedComplement (Q.project ∘ N) CN)
    (hCM : IsGeneralizedComplement (P.project ∘ M) CM) (c : Comparison H) :
    SameMaximum
      (fun R : Superop K H => IsChannel R ∧ IsPhysicalChannel Q.project P.project R)
      (fun R => comparisonRootFidelity c (R ∘ N) (P.project ∘ M))
      (fun S : Superop F E => IsChannel S)
      (fun S => comparisonRootFidelity c CN (S ∘ CM)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end

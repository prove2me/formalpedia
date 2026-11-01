-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_local_information_disturbance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.local_information_disturbance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:19:29.524793+00:00
-- url     : https://prove2.me/theorems/1ba945e1-f75c-466e-b1a1-7c34a5d20e40
-- title:
--   Local information–disturbance duality
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Here $F$ denotes either root entanglement fidelity $F_\rho$ for any normalized input density $\rho$, with an identity reference retained, or worst-case root entanglement fidelity $F_W$ over all normalized logical densities for an arbitrary isometry $W$. Let $\mathcal B$ be a unital complex dagger algebra, and let $\mathcal N,\mathcal M$ be channels on its ambient space whose trace-dual adjoints fix $\mathcal B$ pointwise. Choose arbitrary Stinespring isometries $V_N:H\to H\otimes E_N$ and $V_M:H\to H\otimes E_M$. Their local complements are $\widehat{\mathcal N}^{\mathcal B}=(\mathcal P_{\mathcal B}\otimes\mathrm{id}_{E_N})\circ\mathrm{Ad}_{V_N}$ and similarly for $\mathcal M$, where $\mathcal P_{\mathcal B}$ is the canonical Hilbert–Schmidt projection. Then both maxima are attained and
--
--   $$
--   \max_{\mathcal R^\dagger|_{\mathcal B}=\mathrm{id}}F(\mathcal R\mathcal N,\mathcal M)=\max_{\mathcal S^\dagger(B\otimes I_{E_N})=B\otimes I_{E_M}}F(\widehat{\mathcal N}^{\mathcal B},\mathcal S\widehat{\mathcal M}^{\mathcal B}).
--   $$
--
--   The dual channel acts from $H\otimes E_M$ to $H\otimes E_N$. This is the local information–disturbance tradeoff.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 8, Theorem 8, Eq.(35): local information–disturbance duality (seed result announced on p.1)

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

/-- PDF p.8, Theorem 8, Eq.(35), proof completed p.9. Both F_rho and F_W;
the two identity environments in S†(b ⊗ I_E)=b ⊗ I_F are typed separately. -/
theorem local_information_disturbance [Nonempty H] [Nonempty E] [Nonempty F]
    (A : ObservableAlgebra H) (N M : Superop H H)
    (hN : IsChannel N) (hM : IsChannel M)
    (hNB : FixesObservables (A.algebra : Set (Mat H)) N)
    (hMB : FixesObservables (A.algebra : Set (Mat H)) M)
    (VN : Matrix (H × E) H ℂ) (VM : Matrix (H × F) H ℂ)
    (hVN : IsChannelDilation N VN) (hVM : IsChannelDilation M VM) (c : Comparison H) :
    SameMaximum
      (fun R : Superop H H => IsChannel R ∧ FixesObservables (A.algebra : Set (Mat H)) R)
      (fun R => comparisonRootFidelity c (R ∘ N) M)
      (fun S : Superop (H × F) (H × E) => IsChannel S ∧
        ∀ X ∈ A.algebra,
          operatorTraceDual S (Matrix.kronecker X (1 : Mat E)) =
            Matrix.kronecker X (1 : Mat F))
      (fun S => comparisonRootFidelity c (localComplement A VN) (S ∘ localComplement A VM)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_optimal_physical_photon_cloning
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.optimal_physical_photon_cloning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:00:41.897811+00:00
-- url     : https://prove2.me/theorems/735064bf-7d82-4af7-b14a-edf65fe923a8
-- title:
--   Optimal universal photon cloning from physical Lambda and V evolution
-- statement:
--   Let $A$ be the number of Lambda atoms, or the number of ordered V-atom pairs. Let $m\ge1$ identical photons occupy one unknown normalized polarization $\psi$, and choose $1\le l\le A$, so the output contains $M=m+l$ photons. The Lambda atoms start excited; every V pair starts in $(|e_1e_2\rangle-|e_2e_1\rangle)/\sqrt2$. Use the equal nonzero real coupling $\gamma$, one spatial field mode, the interaction-picture dipole and rotating-wave Hamiltonians (1) and (22), and $e^{-itH}$ with $\hbar=1$.
--
--   There is a time $t>0$, chosen independently of $\psi$, at which the outcome of $A-l$ excited Lambda atoms has a positive polarization-independent probability. Its normalized physical operation is a polarization-covariant channel. The V construction gives the same photonic instrument branch. The input and evolved physical vectors have unit norm, and the conditional physical density is the explicitly embedded sector density $|F_l(\psi)\rangle\langle F_l(\psi)|$. Each sampled photon has density and fidelity
--
--   $$
--   \rho_{\rm sample}=\frac{m(M+2)}{M(m+2)}|\psi\rangle\langle\psi|+\frac{l}{M(m+2)}I_2,
--   \qquad F=\frac{Mm+M+m}{M(m+2)}.
--   $$
--
--   The sampled density also equals that obtained by tracing out the atoms in the normalized physical instrument branch. Every fixed polarization-covariant photon channel from $m$ to $M$ photons has relative-frequency fidelity at most this value for every normalized pure input. Thus the physically constructed operations attain the universal bound. This is the physical representation and sampled-marginal interface; it contains no entropy or capacity conclusion.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 1, Abstract; Secs. II-IV

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1 abstract, pp.2-8 Eqs.(1),(2),(18)-(30): actual Lambda and V
realizations of optimal universal cloning. All physical operations below are
fixed independently of psi. Nonzero gamma is needed only for positive-success
existence; no run-time complexity or entropy/capacity assertion is made. -/
theorem optimal_physical_photon_cloning (A m l : ℕ) (hm : 1 ≤ m)
    (hl : 1 ≤ l) (hlA : l ≤ A) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ 0 < emissionBranchWeight A m l gamma t ∧
      IsChannel (normalizedBranch A m l gamma t) ∧
      PolarizationCovariant m (m + l) (normalizedBranch A m l gamma t) ∧
      vBranch A m l gamma t = physicalBranch A m l gamma t ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        IsState (physicalInput A m psi) ∧
        IsState (physicalOutput A m gamma t psi) ∧
        excitedOutcomeProbability A m l gamma t psi = emissionBranchWeight A m l gamma t ∧
        conditionalPhysical A m l gamma t psi = pureDensity (physicalSector A m l psi) ∧
        (∀ k : Fin (m + l), sampledPhysical A m l gamma t psi k =
          photonSample (m + l)
            (normalizedBranch A m l gamma t (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) k ∧
          sampledPhysical A m l gamma t psi k =
            (((m : ℂ) * (m + l + 2) / ((m + l) * (m + 2))) • pureDensity psi +
             ((l : ℂ) / ((m + l) * (m + 2))) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
          effectProb (pureDensity psi) (sampledPhysical A m l gamma t psi k) =
            benchmark m (m + l))) ∧
      (∀ T : Superop (Fin (m + 1)) (Fin (m + l + 1)),
        IsChannel T → PolarizationCovariant m (m + l) T →
        ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
          photonFrequency (m + l) (T (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) psi ≤
            benchmark m (m + l)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end

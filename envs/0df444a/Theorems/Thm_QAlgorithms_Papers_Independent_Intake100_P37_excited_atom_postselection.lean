-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_excited_atom_postselection
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.excited_atom_postselection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:08:04.768521+00:00
-- url     : https://prove2.me/theorems/d485004a-bcc4-44b7-9710-fdc2fbbbc89a
-- title:
--   Excited-atom postselection and a linear normalized branch
-- statement:
--   Fix $A,m\ge0$, $0\le l\le A$, and real $\gamma,t$. Let $P_l$ be the spectral projection onto exactly $A-l$ excited Lambda atoms. For every normalized unknown polarization $\psi$, the actual evolved vector obeys
--
--   $$
--   P_l\Psi(t,\psi)=f_l(t)F_l(\psi),\qquad
--   p_l(t,\psi)=\|P_l\Psi(t,\psi)\|^2=|f_l(t)|^2.
--   $$
--
--   The same probability is the reference-input weight $p_l(t)$ of the physical photonic instrument branch $T_l$. For every input operator $X$, $\operatorname{Tr}T_l(X)=p_l(t)\operatorname{Tr}X$. If $p_l(t)>0$, the conditional physical density is the normalized density $|F_l(\psi)\rangle\langle F_l(\psi)|$; moreover $X\mapsto p_l(t)^{-1}T_l(X)$ is a polarization-covariant channel. The normalization is by a fixed scalar on all operators. This formalizes fixed output photon count $m+l$ by a measured outcome. Zero-probability outcomes, including $l>0$ at $t=0$, have no asserted normalized conditional state.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 5, Sec. II C, postselection paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5-6: actual excited-atom measurement, input-independent Born
weights, and normalized conditional output only when the outcome has positive
probability. At t=0 all l>0 outcomes have zero probability. -/
theorem excited_atom_postselection (A m l : ℕ) (hlA : l ≤ A) (gamma t : ℝ) :
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      act (selectExcited A m l) (physicalOutput A m gamma t psi) =
        emissionAmplitude A m gamma t ⟨l, by omega⟩ • physicalSector A m l psi ∧
      excitedOutcomeProbability A m l gamma t psi =
        Complex.normSq (emissionAmplitude A m gamma t ⟨l, by omega⟩) ∧
      excitedOutcomeProbability A m l gamma t psi = emissionBranchWeight A m l gamma t ∧
      (0 < excitedOutcomeProbability A m l gamma t psi →
        IsDensityMatrix (conditionalPhysical A m l gamma t psi) ∧
        conditionalPhysical A m l gamma t psi = pureDensity (physicalSector A m l psi))) ∧
    (∀ rho : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      (physicalBranch A m l gamma t rho).trace =
        (emissionBranchWeight A m l gamma t : ℂ) * rho.trace) ∧
    (0 < emissionBranchWeight A m l gamma t →
      IsChannel (normalizedBranch A m l gamma t) ∧
      PolarizationCovariant m (m + l) (normalizedBranch A m l gamma t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_swap_private_chsh
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.swap_private_chsh
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:38:32.443565+00:00
-- url     : https://prove2.me/theorems/405a05a8-b8f1-4ff2-bd49-bdee1e812e6a
-- title:
--   Example Eq. (8): swap private bit CHSH bound
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Let d>=1 be the local shield dimension and let X=F/d^2, where F sends |ij> to |ji>. Define gamma_X by Eq.(7), with its diagonal square-root blocks and external factor 1/2, regrouped on AA′:BB′. For CHSH in correlator normalization (classical bound 2 and quantum bound 2 sqrt(2)),
--
--   $$Q_{\mathrm{CHSH}}(\gamma_X)\le2+\frac{\sqrt2+1}{2\sqrt2\,d}.$$
--
--   This bounds CHSH violation for the particular swap private bit.
--
--   The fixed private-bit formula used here is
--
--   $$\gamma_X=\frac12\left(|00\rangle\langle00|\otimes\sqrt{XX^\dagger}+|00\rangle\langle11|\otimes X+|11\rangle\langle00|\otimes X^\dagger+|11\rangle\langle11|\otimes\sqrt{X^\dagger X}\right),$$
--
--   with the two key qubits and shields regrouped by owner.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 3, Example Eq. (8): swap private bit CHSH bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Entanglement (IsSeparableDensity)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (transposeSecond partyCut xForm swapPrivate hidingOne hidingTwo)

open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Advance50.P47 (Box)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntanglement)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, Eq.(8): swap private bit, correlator CHSH, denominator 2 sqrt(2) d. -/
theorem swap_private_chsh (d : ℕ+) :
    stateValue chshCoefficients (partyCut (swapPrivate d)) ≤
      2 + (Real.sqrt 2 + 1) / (2 * Real.sqrt 2 * (d : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end

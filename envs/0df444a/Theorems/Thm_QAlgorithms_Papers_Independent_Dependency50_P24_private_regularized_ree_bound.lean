-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_private_regularized_ree_bound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.private_regularized_ree_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:14:42.924289+00:00
-- url     : https://prove2.me/theorems/8907ed2d-0dde-4266-ba9b-de749e3cbc55
-- title:
--   Theorem 4: regularized REE of private states
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Under the preceding private-dit assumptions, put $\rho_i=d\langle ii|\gamma|ii\rangle$ and let $E_r^\infty(\omega)=\lim_{n\to\infty}E_r(\omega^{\otimes n})/n$. Then
--
--   $$E_r^{\infty,AA':BB'}(\gamma)\le\log_2 d+\frac1d\sum_{i=0}^{d-1}E_r^{\infty,A':B'}(\rho_i).$$
--
--   Regularization is represented by the equivalent infimum over positive blocklengths, using the source's subadditivity convention. This bound does not require additivity on unlike tensor factors.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 12, Theorem 4: regularized REE of private states

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.12, Theorem 4; pp.38–39: separately regularized conditional shields;
no additivity on unlike factors is assumed. -/
theorem private_regularized_ree_bound {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (gamma : Op (Key d × (S × T))) (hgamma : IsPrivate gamma) :
    regularizedREE (partyCut gamma) ≤ ENNReal.ofReal (logBits d) +
      (d : ℝ≥0∞)⁻¹ * ∑ i, regularizedREE (conditionalShield gamma i) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end

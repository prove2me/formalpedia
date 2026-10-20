-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_binary_qubit_curve_classical
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.binary_qubit_curve_classical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:40:17.047857+00:00
-- url     : https://prove2.me/theorems/dc91ca05-07b6-4363-89f5-4a75fc598739
-- title:
--   Theorem 4(1): a binary-input qubit MI curve is classical
-- statement:
--   Let $X=\{0,1\}$, and let $x\mapsto\rho_x$ be a cq channel into a two-dimensional quantum register $F$, with both matrices positive semidefinite and trace one. There is a measurable classical channel $X\to C$ such that
--
--   $$
--   I(X;F)=I(X;C)\qquad\text{for every input law }p\text{ on }\{0,1\}.
--   $$
--
--   The classical outcome may be represented as a retained real time-sharing flag and a binary outcome; the flag is independent of $X$. Its mutual information is $H(X)$ minus the integral of the posterior binary entropy, not a subtraction of possibly infinite output entropies. A dominating probability measure with normalized measurable densities bounded by two represents the channel. Both input endpoints and $\rho_0=\rho_1$ are allowed.
--
--   This identifies the full mutual-information curve of a binary-input qubit channel with a classical curve. It makes no finite-output-alphabet claim.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 10, Theorem 4(1): a binary-input qubit MI curve is classical

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 4(1), PDF p.10 and Appendix E pp.27–28. Input endpoints are included. -/
theorem binary_qubit_curve_classical (Q : QChannel (Fin 2) (Fin 2)) :
    ∃ K : FlaggedBinaryChannel, ∀ p : Law (Fin 2), qMI p.prob Q.rho id = flaggedMI K p := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_erasure_classical_environment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.erasure_classical_environment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:44:05.213343+00:00
-- url     : https://prove2.me/theorems/4953ae57-2ac9-4695-a486-da795ac8aaa7
-- title:
--   Erasure complement has commuting outputs in every input basis
-- statement:
--   Let $d\ge1$, $0\le\epsilon\le1$, and let $\{|x\rangle\}_{x=1}^d$ be any orthonormal input basis. Use the orthogonally flagged erasure complement $E_{1-\epsilon}$, with flag $|e\rangle$ orthogonal to the data space. For every density operator $\rho$,
--
--   $$
--   E_{1-\epsilon}(\rho)=\epsilon\rho\oplus(1-\epsilon)|e\rangle\langle e|,
--   $$
--
--   where $\rho$ is embedded into the data sector. Moreover, for every pair of basis indices $x,y$,
--
--   $$
--   [E_{1-\epsilon}(|x\rangle\langle x|),E_{1-\epsilon}(|y\rangle\langle y|)]=0.
--   $$
--
--   This gives the classical-environment criterion in any orthonormal input basis, including the one-dimensional case.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 11, Appendix B, unnumbered erasure-channel classical-environment example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.11: the genuine orthogonally flagged complement is the accepted erasureMap
at 1-epsilon. Its action on density matrices has the printed flag weight, and
all outputs from ANY orthonormal input basis commute pairwise. -/
theorem erasure_classical_environment (d : ℕ) (hd : 0 < d)
    (epsilon : ℝ) (hlo : 0 ≤ epsilon) (hhi : epsilon ≤ 1)
    (basis : Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      QAlgorithms.Papers.Independent.Support50.P07.erasureMap d (1 - epsilon) rho =
        (epsilon : ℂ) • erasureData d rho +
          ((1 - epsilon : ℝ) : ℂ) • basisDensity (none : Option (Fin d))) ∧
    (∀ x y : Fin d, Commute
      (QAlgorithms.Papers.Independent.Support50.P07.erasureMap d (1 - epsilon)
        (pureDensity (basisColumn basis x)))
      (QAlgorithms.Papers.Independent.Support50.P07.erasureMap d (1 - epsilon)
        (pureDensity (basisColumn basis y)))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end

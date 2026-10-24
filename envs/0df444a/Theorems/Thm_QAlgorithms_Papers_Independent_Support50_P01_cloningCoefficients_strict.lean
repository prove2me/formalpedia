-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloningCoefficients_strict
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloningCoefficients_strict
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:25:07.190263+00:00
-- url     : https://prove2.me/theorems/24a7d7a5-d127-4317-b217-bd6e5d8b9900
-- title:
--   Appendix Lemma 3: strict ordering of cloning coefficients
-- statement:
--   Let $1\le N\le M$ be integers and $L=M-N$. For $0\le j\le L$ define
--   $$
--   \alpha_j=\frac{N+1}{M+1}\frac{(M-N)!(M-j)!}{(M-N-j)!M!},\qquad
--   \beta_j=\alpha_j\frac{M-j}{M}+\alpha_{j+1}\frac{j+1}{M},
--   $$
--   where $\alpha_{L+1}=0$. Here $\alpha_j$ is the square of the amplitude in Eq.(47). These are scalar vectors; no identification with the inconsistent environment kets printed in Eq.(46) is required. At every adjacent pair within the support,
--   $$\alpha_j>\alpha_{j+1},\qquad\beta_j>\beta_{j+1}\qquad(0\le j<L).$$
--   When $N=M$, the support is a singleton and there is no adjacent pair. This is the source's ordering assertion without extending strict inequalities to padded zeros.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 17, Appendix Lemma 3: strict ordering of cloning coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF pp.16–17, Lemma 3: strict inequalities only at adjacent entries within support.
The N=M singleton case has no adjacent pair. -/
theorem cloningCoefficients_strict (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    ∀ j : ℕ, j<M-N → cloningAlpha N M (j+1) < cloningAlpha N M j ∧
      cloningBeta N M (j+1) < cloningBeta N M j := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end

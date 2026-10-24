-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloningCoefficients_majorization
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloningCoefficients_majorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:26:15.632034+00:00
-- url     : https://prove2.me/theorems/23c1af8a-eccf-4451-b41e-24c2299666d8
-- title:
--   Appendix Lemma 4: majorization of cloning coefficient vectors
-- statement:
--   Let $1\le N\le M$ be integers and $L=M-N$. For $0\le j\le L$ define
--   $$
--   \alpha_j=\frac{N+1}{M+1}\frac{(M-N)!(M-j)!}{(M-N-j)!M!},\qquad
--   \beta_j=\alpha_j\frac{M-j}{M}+\alpha_{j+1}\frac{j+1}{M},
--   $$
--   where $\alpha_{L+1}=0$. Here $\alpha_j$ is the square of the amplitude in Eq.(47). These are scalar vectors; no identification with the inconsistent environment kets printed in Eq.(46) is required. The decreasing probability vectors obey ordinary majorization:
--   $$
--   \sum_{j=0}^{k-1}\beta_j\ge\sum_{j=0}^{k-1}\alpha_j\quad(0\le k\le L+1),\qquad
--   \sum_{j=0}^{L}\alpha_j=\sum_{j=0}^{L}\beta_j=1.
--   $$
--   Both vectors are nonnegative and nonincreasing. Thus $\boldsymbol\beta\succ\boldsymbol\alpha$ denotes majorization with equal totals, not a strict total-sum inequality. No common input-independent degrading channel is inferred.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 17, Appendix Lemma 4: majorization of cloning coefficient vectors

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

/-- PDF pp.16–17, Lemma 4: ordinary probability-vector majorization with equal total sums.
No input-independent quantum degrading map is inferred from a scalar majorization. -/
theorem cloningCoefficients_majorization (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    CloningMajorizes N M := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end

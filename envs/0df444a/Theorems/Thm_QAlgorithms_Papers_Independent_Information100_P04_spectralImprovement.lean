-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_spectralImprovement
-- name    : QAlgorithms.Papers.Independent.Information100.P04.spectralImprovement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:32:28.067979+00:00
-- url     : https://prove2.me/theorems/ba0d831e-1541-43f8-902b-b55d432a316a
-- title:
--   Improvement from the negative spectral subspace
-- statement:
--   Let $\rho$ be a bipartite density matrix with positive negativity $N=(\|\rho^\Gamma\|_1-1)/2$. Let $P$ be the strictly negative spectral projector of $\rho^\Gamma$, let $d=\min(d_A,d_B)$, let $r$ be the rank of $P$, and define $k=\min\{\sqrt r,(d+1)/2\}$, $c=\max\{1,\lambda_{\max}(P^\Gamma)\}$, and $z=-\lambda_{\min}(P^\Gamma)$. Then $0<N\le z$, $1\le c\le k$, $z\le k$, $c\le(d+1)/2$, and $z\le(d-1)/2$. The constructed effect $E=(cI-P^\Gamma)/(c+z)$ satisfies $0\le E\le I$, $0\le E^\Gamma\le cI/(c+z)$, and $\operatorname{Tr}(\rho E)=(c+N)/(c+z)$. Consequently,
--
--   $$\widetilde L(\rho)\ge D_{\rm bin}\!\left(\frac{c+N}{c+z}\middle\|\frac c{c+z}\right).$$
--
--   This divergence is at least both $1-h_2(1/2+N/(2k))$ and $D_{\rm bin}((d+1+2N)/(2d)\|(d+1)/(2d))$. The constructed effect therefore improves the two stated negativity-based comparisons; no comparison with the $s$-dependent term of (46) is asserted.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 15, eq60

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(60) and its two stated comparisons, PDF p.15. The spectral effect is constructed
from rho; the unrelated s-dependent bound in (46) is not compared. -/
theorem spectralImprovement {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hN : 0 < Entanglement.negativity rho) :
    let N := Entanglement.negativity rho
    let d : ℝ := min (Fintype.card A) (Fintype.card B)
    let k := min (Real.sqrt (negativeRank rho)) ((d+1)/2)
    let c := spectralC rho
    let z := spectralZ rho
    let v := binaryD ((c+N)/(c+z)) (c/(c+z))
    0 < z ∧ N ≤ z ∧ 1 ≤ c ∧ c ≤ k ∧ z ≤ k ∧
      c ≤ (d+1)/2 ∧ z ≤ (d-1)/2 ∧
      effectProb (spectralEffect rho) rho = (c+N)/(c+z) ∧ IsEffect (spectralEffect rho) ∧
      (gamma (spectralEffect rho)).PosSemidef ∧
      (((c/(c+z):ℝ):ℂ) • 1 - gamma (spectralEffect rho)).PosSemidef ∧
      v ≤ LTilde rho ∧
      1-binEntropy2 (1/2+N/(2*k)) ≤ v ∧
      binaryD ((d+1+2*N)/(2*d)) ((d+1)/(2*d)) ≤ v := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end

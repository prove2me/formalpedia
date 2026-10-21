-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary10_bestTime
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary10_bestTime
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:51:18.950349+00:00
-- url     : https://prove2.me/theorems/c5e1e475-8d8f-4327-ab67-8e2a4956aca0
-- title:
--   Corollary 10
-- statement:
--   Consider the actual Appendix A.3 construction for an $n$-qubit $k$-local Hermitian $H$, where $n,k\ge1$, $c_e\ge1$, $1\le d_e\le n$, and $H$ has expansion $(c_e,d_e)$. The selected degree $a\in\{1,\ldots,k\}$ maximizes $\sum_{|P|=a}|\alpha_P|^{2d_e/(d_e+1)}$. Set $q=a-1$. For wire $i$ and axis $p\in\{X,Y,Z\}$, let $H_{a,i,p}$ be the weight-$a$ Pauli slice with $P_i=p$, with wire $i$ deleted. The first $q$ replicas are independent single-qubit Haar pure states $\rho_{s,j}$. The number $\beta_{i,p}$ is the signed uniform average in Eq.(A24), and the last replica at wire $i$ is the pure maximizer of $\sum_p\beta_{i,p}p$. A zero field is resolved by any pure maximizer. With all $a$ replicas, define
--   $$\rho(t;\rho_{\cdot,\cdot},\sigma)=\bigotimes_j\left[\frac I2+\frac ta\sum_{s=1}^a\sigma_s(\rho_{s,j}-I/2)\right].$$
--   For fixed replicas and signs, let $t_*$ be an attained maximizer of $|\operatorname{tr}(H\rho(t))-\alpha_I|$ over $t\in[-1,1]$. Then
--   $$|\operatorname{tr}(H\rho(t_*))-\alpha_I|\ge(1+\sqrt2)^{-k}|\operatorname{tr}(H_a\rho(1))|.$$
--   This connects optimization along the actual polynomial path with the chosen homogeneous slice; it assigns no unit computational cost to finding an exact real optimizer.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 30, Corollary 10

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 10, paper p.30, A91: the actual A.3 path, replicas, signs,
and constructed compact-interval optimizer, rather than an arbitrary maximizing state. -/
theorem corollary10_bestTime (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1)
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (hrho : ∀ s j, IsPureQubit (rho s j))
    (sigma : Fin (q + 1) → Bool) :
    let full := completedReplicas H rho
    |effectProb (homogeneousSlice (q + 1) H) (productPath 1 full sigma)| /
      (1 + Real.sqrt 2) ^ k ≤
      |effectProb H (productPath (bestTime H full sigma) full sigma) -
        coefficient H (fun _ => 0)| := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end

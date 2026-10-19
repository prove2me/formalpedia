-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_scalarTestingReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P58.scalarTestingReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:22:38.212834+00:00
-- url     : https://prove2.me/theorems/a3d21747-cac1-448d-856d-d395c50e673b
-- title:
--   Scalar reduction of the quantum testing problem
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For a unit vector $\psi\in\mathbb C^d$, put $\omega_\psi=\mathcal E_p^{\otimes n}((|\psi\rangle\langle\psi|)^{\otimes n})$. For a probability distribution $q=(q_S)$ on all survivor sets, including the empty set, put $\sigma_q=\bigoplus_S q_S I_S/D_S$. For density operators $\omega,\sigma$ and $0\le\varepsilon<1$, define $\beta_\varepsilon(\omega\Vert\sigma)=\min\{\operatorname{Tr}(T\sigma):0\le T\le I,\operatorname{Tr}(T\omega)\ge1-\varepsilon\}$ and $D_H^\varepsilon=-\log_2\beta_\varepsilon$, with $-\log_2 0=+\infty$. For every auxiliary probability distribution $q$,
--
--   $$\beta_\varepsilon(\omega_\psi\Vert\sigma_q)=\min\left\{\sum_S\frac{q_St_S}{D_S}:0\le t_S\le1,\ \sum_Sw_St_S\ge1-\varepsilon\right\}.$$
--
--   The minimum is attained by a finite family $(t_S)$. The identity includes the empty sector and vanishing $q_S$ or $w_S$; there is no division by these weights. It reduces an independently defined operator-test optimum, rather than defining testing through the scalar program.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 22, §5.3, Eq. (5.21)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Eq.(5.21), PDF p.22: actual quantum testing reduces to a finite scalar minimum, with attainment. -/
theorem scalarTestingReduction (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1) (q : Distribution (Finset (Fin n))) :
    testingBeta ε (reference n d p ψ) (auxiliary n d q.val) =
      sInf {v : ℝ | ∃ t : Finset (Fin n) → ℝ, ScalarFeasible n p ε t ∧ v=scalarCost n d q.val t} ∧
    ∃ t : Finset (Fin n) → ℝ, ScalarFeasible n p ε t ∧
      scalarCost n d q.val t = testingBeta ε (reference n d p ψ) (auxiliary n d q.val) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58

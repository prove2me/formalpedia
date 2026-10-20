-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_thirdOrderCapacity
-- name    : QAlgorithms.Papers.Independent.Information100.P63.thirdOrderCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:32:41.146232+00:00
-- url     : https://prove2.me/theorems/cccdfef3-65ac-415c-854c-ab55ebe25a1f
-- title:
--   Third-order classical capacity of the depolarizing channel
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   Let $M^*(n,\varepsilon)$ be the maximum positive integer $M$ for which there are arbitrary input states $\rho_x$ and an $M$-outcome collective POVM $\{\Lambda_x\}$ with average error $1-M^{-1}\sum_x\operatorname{Tr}[\Lambda_x\mathcal D_{p,d}^{\otimes n}(\rho_x)]\le\varepsilon$. Messages are equiprobable, no entanglement is shared between sender and receiver, and repeated states and zero POVM effects are allowed.
--
--   Fix $0<p\le p_{\max}(d)$, $p\ne1$, and $0<\varepsilon<1$. Set $c=\log d+\alpha\log\alpha+(d-1)\beta\log\beta$ and $v=\alpha(1-\alpha)(\log\alpha-\log\beta)^2$. If $\Phi^{-1}$ is the standard normal quantile, then there are $C>0$ and $n_0\ge4$, depending only on $d,p,\varepsilon$, such that for every $n\ge n_0$,
--
--   $$
--   \left|\log M^*(n,\varepsilon)-nc-\sqrt{nv}\,\Phi^{-1}(\varepsilon)-\tfrac12\log n\right|\le C\log\log n.
--   $$
--
--   This gives both sides of the third-order expansion for the full unassisted classical coding optimization.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 3, Theorem 2, Eq. (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2, Eq.(5), PDF pp.3,11: two-sided third-order expansion; constants depend
only on the fixed `d,p,ε`, and the logarithmic coefficient is exactly `1/2`. -/
theorem thirdOrderCapacity (d : ℕ) (hd : 2 ≤ d) (p e : ℝ)
    (hp : 0 < p) (hpmax : p ≤ pMax d) (hpone : p ≠ 1) (he : 0 < e) (heone : e < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 4 ≤ n0 ∧ ∀ n ≥ n0,
      |logTwo (quantumMessages d n p e) - thirdOrder d n p e| ≤ C * logTwo (logTwo n) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end

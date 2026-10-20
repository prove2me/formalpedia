-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_degenerateCapacities
-- name    : QAlgorithms.Papers.Independent.Information100.P63.degenerateCapacities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:42:53.668156+00:00
-- url     : https://prove2.me/theorems/3086ddc7-5f04-45bb-ad57-6369bb135734
-- title:
--   Exact degenerate-channel optimal message sizes
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   Let $M^*(n,\varepsilon)$ be the maximum positive integer $M$ for which there are arbitrary input states $\rho_x$ and an $M$-outcome collective POVM $\{\Lambda_x\}$ with average error $1-M^{-1}\sum_x\operatorname{Tr}[\Lambda_x\mathcal D_{p,d}^{\otimes n}(\rho_x)]\le\varepsilon$. Messages are equiprobable, no entanglement is shared between sender and receiver, and repeated states and zero POVM effects are allowed.
--
--   For every integer $n\ge0$ and $0\le\varepsilon<1$,
--
--   $$
--   M^*_{p=0}(n,\varepsilon)=\left\lfloor\frac{d^n}{1-\varepsilon}\right\rfloor,\qquad M^*_{p=1}(n,\varepsilon)=\left\lfloor\frac1{1-\varepsilon}\right\rfloor.
--   $$
--
--   These are exact average-error endpoint formulas. The third-order theorem makes no uniform remainder claim near these endpoints.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 4, Footnote 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Footnote 1, PDF p.4: exact average-error formulas at the identity and completely
randomizing endpoints; zero decoding effects and repeated codewords remain allowed. -/
theorem degenerateCapacities (d n : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 ≤ e) (heone : e < 1) :
    quantumMessages d n 0 e = ⌊(d : ℝ)^n / (1-e)⌋₊ ∧
    quantumMessages d n 1 e = ⌊1 / (1-e)⌋₊ := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end

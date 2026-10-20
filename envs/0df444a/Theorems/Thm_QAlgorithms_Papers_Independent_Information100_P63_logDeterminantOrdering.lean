-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_logDeterminantOrdering
-- name    : QAlgorithms.Papers.Independent.Information100.P63.logDeterminantOrdering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:35:57.138355+00:00
-- url     : https://prove2.me/theorems/413720d6-e8d6-47dc-9fbc-820b0c40f2ea
-- title:
--   Log-determinant ordering of depolarizing outputs
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   For every $n\ge1$, every state $\rho$ on $(\mathbb C^d)^{\otimes n}$, every $0<p\le p_{\max}(d)$, and every $t>0$,
--
--   $$
--   L_t(\mathcal D_{p,d}^{\otimes n}(\rho))\ge L_t(\tau^{\otimes n}).
--   $$
--
--   This ordering holds at every positive shift, including for entangled inputs and at $p=1$.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 5, Theorem 4, Eq. (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4, Eq.(20), PDF pp.5–6; includes `p=1` and all entangled states. -/
theorem logDeterminantOrdering (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (p t : ℝ) (hp : 0 < p) (hpmax : p ≤ pMax d) (ht : 0 < t)
    (X : Mat (Fin n → Fin d)) (hX : IsDensityMatrix X) :
    logDet t (reference d n p) ≤ logDet t (depolarizingN d n p X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end

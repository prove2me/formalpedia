-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_nonvanishingDefect
-- name    : QAlgorithms.Papers.Independent.Information100.P63.nonvanishingDefect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:45:18.522629+00:00
-- url     : https://prove2.me/theorems/267b0fa7-7a93-42f1-ad0d-ea2fe5f1ed42
-- title:
--   All Schatten bounds with nonvanishing defect
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   Fix $0<p\le p_{\max}(d)$, $p\ne1$. There is a single sequence of states $W_n$ on $(\mathbb C^d)^{\otimes n}$ and a threshold $n_0$ such that for every $n\ge n_0$, $W_n$ is positive definite and
--
--   $$
--   \|W_n\|_q\le\|\tau^{\otimes n}\|_q\quad(1\le q<\infty),\qquad\|W_n\|_\infty\le\|\tau^{\otimes n}\|_\infty,\qquad\delta_{\rm maj}(W_n,\tau^{\otimes n})\longrightarrow\frac12.
--   $$
--
--   Here finite Schatten norms are defined from the positive spectrum, and $\|X\|_\infty$ is its largest eigenvalue. The sequence need not consist of channel outputs.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 15, Proposition 12, Eqs. (78)–(79)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 12, Eqs.(78)–(79), PDF p.15: one full sequence, all finite Schatten
exponents and the operator norm, and convergence of the same sequence's defect. -/
theorem nonvanishingDefect (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) (hpmax : p ≤ pMax d) (hpone : p ≠ 1) :
    ∃ W : (n : ℕ) → Mat (Fin n → Fin d),
      (∀ n, IsDensityMatrix (W n)) ∧
      (∃ n0 : ℕ, ∀ n ≥ n0, (W n).PosDef ∧
        (∀ q : ℝ, 1 ≤ q → schatten q (W n) ≤ schatten q (reference d n p)) ∧
        schattenInfinity (W n) ≤ schattenInfinity (reference d n p)) ∧
      Tendsto (fun n => defect (W n) (reference d n p)) atTop (nhds (1/2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end

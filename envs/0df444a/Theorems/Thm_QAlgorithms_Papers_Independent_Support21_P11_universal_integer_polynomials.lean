-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_universal_integer_polynomials
-- name    : QAlgorithms.Papers.Independent.Support21.P11.universal_integer_polynomials
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:01:12.351027+00:00
-- url     : https://prove2.me/theorems/91ecff7a-9a8d-4f15-94ae-14e60dea487e
-- title:
--   Constructed universal symmetric integer polynomials
-- statement:
--   Fix $r\ge1$. In $\mathbb Z[u_1,\ldots,u_r]$ put $\prod_i(z-u_i)=\sum_{j=0}^ra_jz^j$. Construct $H_k$ successively: if $k<r$, put $j=r-1-k$ and
--
--   $$H_k=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}-\sum_{\mu=0}^{k-1}H_\mu a_{\mu+j+1};\qquad H_k=-\sum_{j=0}^{r-1}a_jH_{j+k-r}\quad(k\ge r).$$
--
--   The symbol $\delta$ is the indicator; an empty sum is zero. Every $H_a$ is symmetric in the variables. For every commutative unital ring $R$, arbitrary sequence $\omega$ and parameters $u_i\in R$ satisfying this paper's admissibility relations,
--
--   $$\omega_a=H_a(u_1,\ldots,u_r)\qquad(a\ge0).$$
--
--   The same integer polynomials work in all ground rings, without any division or domain assumption.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 7, Lemma 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 4.4, PDF p.7. The concrete integer polynomials precede every
coefficient ring and parameter system; symmetry and all evaluations are conclusions. -/
theorem universal_integer_polynomials (r : ℕ) (hr : 1 ≤ r) :
    (∀ (a : ℕ) (sigma : Equiv.Perm (Fin r)),
      MvPolynomial.rename sigma (universalH r a) = universalH r a) ∧
    (∀ (R : Type*) [CommRing R] (omega : ℕ → R) (u : Fin r → R),
      BMWAdmissible omega u → ∀ a : ℕ, omega a = evalH u a) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_generic_field_schur_formula
-- name    : QAlgorithms.Papers.Independent.Support21.P11.generic_field_schur_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:59:34.362969+00:00
-- url     : https://prove2.me/theorems/bbef8ccf-1900-4994-b33a-d4fc19002275
-- title:
--   Schur expression under generic field independence
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $r\ge1$, and let $\omega=(\omega_a)_{a\ge0}$ and $u_1,\ldots,u_r\in F$ be parameters. Assume the $u_i$ are pairwise distinct and $u_i+u_j\ne0$ for every $i,j$, including $i=j$. Let $W$ be the associated two-strand degenerate cyclotomic BMW algebra and write $e=e_1$, $x=x_1$. Suppose $(e,xe,\ldots,x^{r-1}e)$ is independent over $F$ and $eWe
--   e0$. Define the Schur polynomials $q_a$ by $\prod_i(1+u_it)/(1-u_it)=\sum_{a\ge0}q_a(u)t^a$, and put $\eta_a(u)=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}$. The symbol $\delta$ denotes the indicator of its subscripted condition. Then
--
--   $$\omega_a=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}\qquad(a\ge0).$$
--
--   This is the explicit Schur formula for the sequence forced by the generic field hypotheses.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 5, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Corollary 3.3, equation (3.6), PDF p.5. The coefficient of q_(a+1)
is 1; those of (-1)^r q_a and delta_(a,0) have magnitude 1/2. -/
theorem generic_field_schur_formula (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (hdistinct : Function.Injective u) (hsum : ∀ i j : Fin r, u i + u j ≠ 0)
    (hli : LinearIndependent F (idealFamily F omega r u))
    (hcorner : NonzeroCorner F omega r u) :
    ∀ a : ℕ, omega a = schurEta u a := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end

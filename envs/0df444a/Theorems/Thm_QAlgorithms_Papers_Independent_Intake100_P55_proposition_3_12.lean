-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_12
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:53:40.174945+00:00
-- url     : https://prove2.me/theorems/fff9db1b-11a6-4f1d-8d5e-7814ca916e2d
-- title:
--   Proposition 3.12
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n,r\ge1$, work in $\widehat W_{n+1}$ and define $x_n=(g_{n-1}\cdots g_1)x_1(g_1\cdots g_{n-1})$. Then
--   $$\begin{aligned}g_nx_ng_nx_n&=x_ng_nx_ng_n,\e_nx_ng_nx_n&=\lambda^{-1}e_n,\e_nx_n^rg_nx_n&=\lambda^{-2}e_nx_n^{r-1}g_n^{-1},\e_nx_n^{-r}g_n^{-1}x_n^{-1}&=\lambda^2e_nx_n^{-r+1}g_n.\end{aligned}$$
--   These are the general affine braid and unwrapping identities.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 20, Proposition 3.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.12(1)--(4), PDF p.20, verified in the page image.
The displayed e_n,g_n live in W_(n+1); r≥1 makes r-1 nontruncated. -/
theorem proposition_3_12 (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    let g := ghCrossing P q true (n+1) n false
    let gi := ghCrossing P q true (n+1) n true
    let e := ghContraction P q true (n+1) n
    let x := bmwWinding P q (n+1) false n
    let xi := bmwWinding P q (n+1) true n
    g*x*g*x = x*g*x*g ∧
    e*x*g*x = algebraMap R _ (↑P.lam⁻¹ : R)*e ∧
    e*x^r*g*x = algebraMap R _ ((↑P.lam⁻¹ : R)^2)*e*x^(r-1)*gi ∧
    e*xi^r*gi*xi = algebraMap R _ ((P.lam : R)^2)*e*xi^(r-1)*g := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end

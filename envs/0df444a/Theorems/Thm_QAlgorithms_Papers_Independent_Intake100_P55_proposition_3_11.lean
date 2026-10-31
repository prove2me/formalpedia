-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_11
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:53:05.04298+00:00
-- url     : https://prove2.me/theorems/ee98858c-189e-4bdf-8c06-0d98d0ff5421
-- title:
--   Proposition 3.11
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For $1\le r<n$ in $\widehat W_n$, use the winding elements $x_s=(g_{s-1}\cdots g_1)x_1(g_1\cdots g_{s-1})$. Then all eight identities hold:
--   $$\begin{aligned}g_rx_r&=x_{r+1}g_r^{-1},&g_r^{-1}x_{r+1}&=x_rg_r,\g_rx_{r+1}&=x_rg_r-zx_{r+1}+ze_rx_{r+1},&g_r^{-1}x_r&=x_{r+1}g_r^{-1}+zx_r-ze_rx_r,\e_rx_r&=\lambda^{-2}e_rx_{r+1}^{-1},&x_re_r&=\lambda^{-2}x_{r+1}^{-1}e_r,\e_rx_r^{-1}&=\lambda^2e_rx_{r+1},&x_r^{-1}e_r&=\lambda^2x_{r+1}e_r.\end{aligned}$$
--   They describe adjacent-generator interactions with positive and negative windings.
--
--   Source correction: the printed coefficient $z\lambda$ of $e_rx_{r+1}$ is replaced by $z$, as required by Definition 3.6(6) and clause (1). All other clauses and hypotheses are retained.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 19, Proposition 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.11(1)--(4), PDF p.19, with all eight identities.
Source correction in (2): printed z*lambda*e_r*x_(r+1) is changed to
z*e_r*x_(r+1). Multiplying the defining skein relation by x_(r+1)
and using (1) requires coefficient z; the printed extra lambda fails
in a nonzero two-strand scalar representation. -/
theorem proposition_3_11 (n r : ℕ) (hr : BMWIndex n r) :
    let g := ghCrossing P q true n r false
    let gi := ghCrossing P q true n r true
    let e := ghContraction P q true n r
    let x := bmwWinding P q n false r
    let y := bmwWinding P q n false (r+1)
    let xi := bmwWinding P q n true r
    let yi := bmwWinding P q n true (r+1)
    let z := algebraMap R (OrdinaryAffineBMW P q true n) P.z
    let l := algebraMap R (OrdinaryAffineBMW P q true n) (P.lam : R)
    let li2 := algebraMap R (OrdinaryAffineBMW P q true n) ((↑P.lam⁻¹ : R)^2)
    g*x = y*gi ∧ gi*y = x*g ∧
    g*y = x*g - z*y + z*e*y ∧ gi*x = y*gi + z*x - z*e*x ∧
    e*x = li2*e*yi ∧ x*e = li2*yi*e ∧
    e*xi = l^2*e*y ∧ xi*e = l^2*y*e := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end

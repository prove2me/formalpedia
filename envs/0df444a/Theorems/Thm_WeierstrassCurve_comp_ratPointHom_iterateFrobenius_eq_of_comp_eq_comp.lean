-- Prove2me | Theorems.Thm_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
-- name    : WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e92d5514-9b80-5acc-ade4-b1420b2f3fe4
-- title:
--   Conjugation by an isogeny agrees with Frobenius transport
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $p$, with $p$ prime, let $n$ be a natural number, and write $\sigma =$ `iterateFrobenius k p n` for the ring endomorphism $x \mapsto x^{p^{n}}$ of $k$. Let $W$ be a Weierstrass curve over $k$ satisfying `IsElliptic`, and let $W.map\ \sigma$ be the curve obtained by applying $\sigma$ to the coefficients. Assume there is a point $T$ of the affine group $W(k)$ with $T \neq 0$ and $p \cdot T = 0$. Let $\rho : W(k) \to (W.map\ \sigma)(k)$ be an additive map lying in `rationalHomSet`, i.e. either zero or rationally represented: there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $k$ and a finite set $B \subseteq k$ such that for every nonsingular point $(x,y)$ with $x \notin B$ the denominators $d_X, d_Y$ do not vanish at $(x,y)$ and $\rho(x,y) = (n_X/d_X, n_Y/d_Y)$ evaluated there; assume moreover $\rho \neq 0$. Let $\beta$ be an additive endomorphism of $W(k)$ and $\beta'$ an additive endomorphism of $(W.map\ \sigma)(k)$, both in the corresponding `rationalHomSet`, and suppose $\beta' \circ \rho = \rho \circ \beta$. Then $\beta' \circ \Phi = \Phi \circ \beta$, where $\Phi =$ `ratPointHom` $\sigma$ is the additive map sending $0$ to $0$ and $(x,y)$ to $(x^{p^{n}}, y^{p^{n}})$.
--
--   This is the Deuring–Waterhouse observation that for an ordinary elliptic curve — ordinarity being expressed here by the existence of a nonzero $k$-point killed by $p$ — the isomorphism between the endomorphism algebras of $W$ and of its Frobenius twist induced by conjugation with a nonzero isogeny is independent of the isogeny, and hence coincides with the coefficientwise transport computed with the $p^{n}$-power Frobenius. It is used in the project's characteristic $2$ analysis of Weierstrass curves, namely in [`WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (W : WeierstrassCurve k) [W.IsElliptic] {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0) {ρ : W.toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W (W.map (iterateFrobenius k p n))) (hρ0 : ρ ≠ 0) {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) {β' : (W.map (iterateFrobenius k p n)).toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point} (hβ' : β' ∈ WeierstrassCurve.rationalHomSet k (W.map (iterateFrobenius k p n)) (W.map (iterateFrobenius k p n))) (h : β'.comp ρ = ρ.comp β) : β'.comp (WeierstrassCurve.ratPointHom (iterateFrobenius k p n)) = (WeierstrassCurve.ratPointHom (iterateFrobenius k p n)).comp β := by sorry

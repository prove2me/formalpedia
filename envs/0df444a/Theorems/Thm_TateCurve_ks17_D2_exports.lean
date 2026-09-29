-- Prove2me | Theorems.Thm_TateCurve_ks17_D2_exports
-- name    : TateCurve.ks17_D2_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/eab0abef-59e6-517f-9a2c-140ca5e2fe95
-- title:
--   Half-lattice closure of the Tate addition identities
-- statement:
--   Throughout, $K$ is a nontrivially normed, ultrametric, complete field of characteristic zero with decidable equality, and for $q,u\in K$ one writes $X(u)=\bigl(\sum_{n\in\mathbb Z}x(q^nu)\bigr)-2s_1(q)$ and $Y(u)=\bigl(\sum_{n\in\mathbb Z}y(q^nu)\bigr)+s_1(q)$ for the Tate point series, $\mathrm{symSumNum}_q(x_1,x_2)=2x_1x_2(x_1+x_2)+x_1x_2+2a_4(q)(x_1+x_2)+4a_6(q)$, and calls $(u,v)$ admissible (`AddParams`) when $q,u,v\neq0$ and $q^nw\neq1$ for all $n\in\mathbb Z$ and $w\in\{u,v,uv,uv^{-1}\}$, and regional (`ExpansionRegion`) when moreover $\|q\|<1$ and $\|q\|<\|w\|$, $\|q\|\,\|w\|<1$ for those same four $w$. The theorem is the conjunction of three assertions. First: given $q,\tau$ with $q\neq0$, $\|q\|<1$, $\tau^2=q$, and given that the identities $(X(uv)+X(uv^{-1}))(X(u)-X(v))^2=\mathrm{symSumNum}_q(X(u),X(v))$ and $(X(uv)-X(uv^{-1}))(X(u)-X(v))^2=-(2Y(u)+X(u))(2Y(v)+X(v))$ hold for all regional pairs, the predicate `DiffHyp` $q$ holds, i.e. the second identity holds at every admissible pair. Second: if $K$ is in addition algebraically closed, every $q\in K$ has a square root. Third: under the same hypotheses on $q,\tau$ and the same two regional identities, the first identity holds at any admissible pair $(u,v)$.
--
--   These are the interface lemmas of the half-lattice ($u^2\in q^{\mathbb Z}$) layer of the analytic addition law on the Tate curve $y^2+xy=x^3+a_4(q)x+a_6(q)$: they propagate the symmetric sum and difference identities from the annular expansion region, where the point series may be expanded and regrouped, to all admissible parameter pairs, using a square root of $q$ for the $\mu_2$-translation step. They are used by [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional), [`TateCurve.symAdd_sum_allParams_unconditional`](thm.html#TateCurve.symAdd_sum_allParams_unconditional) and [`TateCurve.symAdd_sum_regional`](thm.html#TateCurve.symAdd_sum_regional), which supply the group law for the Tate parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_D2_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_D2_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))),
      DiffHyp q) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] (q : K),
      ∃ τ : K, τ ^ 2 = q) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q u v τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v)) := by sorry

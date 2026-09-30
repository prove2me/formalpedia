-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_minimum_chart_cost_contact_lower_bound
-- name    : WeierstrassEllipticZeta.minimum_chart_cost_contact_lower_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T00:26:07.387373+00:00
-- url     : https://prove2.me/theorems/09f516c3-b1c3-463b-a4cd-e92c183406ae
-- title:
--   High analytic contact forces minimum chart cost at least T+1
-- statement:
--   Let L be a period pair, D normalized sigma differential data, and S the entire projective Weierstrass coordinates. Let Q be homogeneous of degree n in the last five variables and suppose its entire projective pullback is not identically zero. Let X be a finite subset of C containing zero, and let N be a correct common cap for the two chart jet ideals of Q at every derivative order.
--
--   If Q has analytic order at least 3T+1 at every point of X+X+X in each available denominator chart, then:
--
--   1. Every capped chart budget e at a valid point of X+X+X satisfies T+1 <= e.
--   2. Every canonical chart cost at such a point is at least T+1.
--   3. The minimum canonical chart cost over all valid chart points is at least T+1.
--
--   There is no positivity assumption on T or n. The cap correctness is an explicit hypothesis, and the minimum is nonempty because the normalized second chart is available at zero.
--
--   The previous selection theorem exposed the generic lower bound 1. This result gives the stronger lower bound T+1 under the stated contact hypotheses. It is a local multiplicity theorem; it does not bound costs above by section dimension, improve the section coefficient 5, or change the integer-search range.
-- source:
--   Derived local multiplicity interface for Senthil Kumar K (2026), Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a derived formal lemma, not a quotation or an assertion that the paper defines the canonical chart cost. High contact of order 3*T+1 gives a persistent prime in one of three derivative blocks. Finite analytic order yields a transverse derivative; prime localization and the contact length theorem give T+1 <= length <= e for every valid capped chart budget. Consequently each canonical chart cost and their attained minimum are at least T+1. This strengthens the previously exposed generic lower bound 1 when the A.1 contact hypotheses hold. It does not improve a global upper bound. The direct stabilizer sketch preserves C and reuses the existing Open capped-chart degree budget https://prove2.me/theorems/f6b31fa8-82d8-415d-bc46-f147aa9dfad7. No new Open child, section coefficient change or integer-search improvement is claimed.

import Definitions.Def_WeierstrassEllipticZeta_MinimumChartCost
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Order
open WeierstrassEllipticZeta
open scoped Pointwise

theorem WeierstrassEllipticZeta.minimum_chart_cost_contact_lower_bound
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n N T : ℕ) (X : Finset ℂ)
    (h0 : 0 ∈ X)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (hcap : ∀ (c : Fin 2) (t : ℕ), extensionChartJetIdeal L Q c t =
      extensionChartJetIdeal L Q c (min t N))
    (hhigh : ∀ z ∈ X + X + X, ∀ c : Fin 2,
      S (extensionChartDenominator c) z ≠ 0 →
      ((3 * T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun w : ℂ => MvPolynomial.eval
          ![1, w, S 0 w / S (extensionChartDenominator c) w,
            S 1 w / S (extensionChartDenominator c) w,
            S 2 w / S (extensionChartDenominator c) w,
            S 3 w / S (extensionChartDenominator c) w,
            S 4 w / S (extensionChartDenominator c) w] Q) z) :
    (∀ e : ℕ, CappedChartJetBudget L S Q N T e (X + X + X) → T + 1 ≤ e) ∧
    (∀ (c : Fin 2) (z : ℂ), z ∈ X + X + X →
      S (extensionChartDenominator c) z ≠ 0 →
      T + 1 ≤ cappedChartCost L S Q N T c z) ∧
    T + 1 ≤ minimumChartCost L S Q N T X := by sorry

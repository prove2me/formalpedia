-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_fibre_present_minimum_anchor_weight
-- name    : WeierstrassEllipticZeta.fibre_present_minimum_anchor_weight
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T02:02:08.34569+00:00
-- url     : https://prove2.me/theorems/25ac1c54-cc14-4330-856b-bbb857aa59b0
-- title:
--   Explicit point and whole-fibre minimum anchor weights
-- statement:
--   Use the mission's existing sparse-GCD anchor candidates and minimumAnchorWeight. Let Lambda be any integer submodule of C, eta a linear map from Lambda to C, X a finite set, S and Q arbitrary coordinate functions and polynomial, m,n natural numbers, K a coordinate region, and Z the supplied finite fibre list. Write
--
--       N = card(X),
--       q = card(image of X in C/Lambda),
--       M = (m+1)*q,
--       W = minimumAnchorWeight Lambda eta X S Q m n K Z.
--
--   Then:
--
--   1. min(N,M) <= W, without any additional hypothesis.
--   2. If N <= M, then W=N: the point candidate attains the optimum.
--   3. If Z is nonempty, then W=min(N,M): a point or any supplied fibre candidate attains the optimum.
--
--   Every line candidate has period kernel contained in Lambda, so its quotient class count is at least q and its weight is at least M. Thus line coordinates need not be searched in either of the two cases above. Line-anchor selection can remain relevant only when Z is empty and N>M.
--
--   This abstract result concerns the defined candidate weights; it does not itself certify that an arbitrary supplied Z enumerates vanishing fibres. The A.1 application retains that exactness hypothesis. No analytic assumptions, nonempty X, positive-degree assumptions, or effective coordinate-feasibility algorithm are needed or asserted here. The formulas are derived for the formalization, not quoted from the paper.
-- source:
--   Derived optimizer lemma for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a derived result about the formalization's existing candidate weights, not a quoted paper formula. Every elementary period kernel is contained in the lattice, so its image class count is at least the lattice class count q. Nonpoint weights are therefore at least (m+1)*q. The point has weight |X| and any available whole fibre has weight (m+1)*q. Consequently min(|X|,(m+1)*q)<=W_min; the point is optimal if |X|<=(m+1)*q, and a nonempty fibre list gives W_min=min(|X|,(m+1)*q). The global geometric estimate and all constants remain open/unchanged.

import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
import Mathlib.LinearAlgebra.Quotient.Basic
open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.fibre_present_minimum_anchor_weight
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    min X.card ((m + 1) * (X.image Λ.mkQ).card) ≤
        minimumAnchorWeight Λ η X S Q m n K Z ∧
      (X.card ≤ (m + 1) * (X.image Λ.mkQ).card →
        minimumAnchorWeight Λ η X S Q m n K Z = X.card) ∧
      (Z.Nonempty → minimumAnchorWeight Λ η X S Q m n K Z =
        min X.card ((m + 1) * (X.image Λ.mkQ).card)) := by sorry

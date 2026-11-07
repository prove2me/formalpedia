-- Prove2me | Theorems.Thm_SigmoidWire_proposition_B_4
-- name    : SigmoidWire.proposition_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:23.244664+00:00
-- url     : https://prove2.me/theorems/a45378a2-37f1-410c-ad1c-59cbd2b65230
-- title:
--   Proposition B.4: a rational approximate sign function
-- statement:
--   There is a constant $C$ such that for every $B\ge2$ and $\eta\in(0,1)$ there is a rational function $S$ of degree at most $C\ln^2(B/\eta)$, with no pole in $[-B,B]$, such that for every $y\in[-B,B]$:
--
--   1. $S(y)\in[-\eta,1+\eta]$;
--   2. $S(y)\in[1-\eta,1+\eta]$ if $y\ge1$;
--   3. $S(y)\in[-\eta,\eta]$ if $y\le-1$.
--
--   The function $S$ is the switch that glues two approximations of Sigmoid into one in Lemma 4.5.
--
--   Differences from the source:
--   - encoding: a rational function S of degree O(ln²(B/η)) → polynomials P, Q with both natDegrees ≤ C·ln²(B/η), C chosen before B and η; reason: degree of P/Q is max{deg P, deg Q} (p.19), and ln(B/η) > ln 2 > 0 on this domain
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Proposition B.4, p.60

import Mathlib

namespace SigmoidWire

/-- **Proposition B.4 (approximate sign function).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Proposition B.4, p.60
(PDF p.62): "For every B ≥ 2 and η ∈ (0, 1), there is a rational function S of degree O(ln²(B/η))
with no pole in [−B, B] such that for every y ∈ [−B, B], S(y) ∈ [−η, 1 + η]; moreover,
S(y) ∈ [1 − η, 1 + η] if y ≥ 1, and S(y) ∈ [−η, η] if y ≤ −1."

**Formalization Note.** `S = P/Q` with real polynomials `P, Q`; the `O(ln²(B/η))` is a single
constant `Cc` chosen before `B` and `η` with both degrees `≤ Cc · ln²(B/η)` (on this domain
`ln(B/η) > ln 2 > 0`); "no pole in `[−B, B]`" is `Q ≠ 0` there. The two "moreover" clauses are
claimed for `y ∈ [−B, B]`. -/
theorem proposition_B_4 :
    ∃ Cc : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ η : ℝ, 0 < η → η < 1 →
      ∃ P Q : Polynomial ℝ,
        (P.natDegree : ℝ) ≤ Cc * Real.log (B / η) ^ 2 ∧
        (Q.natDegree : ℝ) ≤ Cc * Real.log (B / η) ^ 2 ∧
        ∀ y ∈ Set.Icc (-B) B, Q.eval y ≠ 0 ∧
          P.eval y / Q.eval y ∈ Set.Icc (-η) (1 + η) ∧
          (1 ≤ y → P.eval y / Q.eval y ∈ Set.Icc (1 - η) (1 + η)) ∧
          (y ≤ -1 → P.eval y / Q.eval y ∈ Set.Icc (-η) η) := by sorry

end SigmoidWire

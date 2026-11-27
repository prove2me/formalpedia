-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_Supplement_theorem_EC_3_refuted
-- name    : ReusableAssort.Hybrid.Supplement.theorem_EC_3_refuted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:22:25.529118+00:00
-- url     : https://prove2.me/theorems/9e5eeeea-964c-4d2c-a993-22dd2ce1bfb6
-- title:
--   Theorem EC.3 (corrected: refutation), ec27 — Algorithm 5 as printed double-counts offer probabilities
-- statement:
--   The printed Theorem EC.3 fails for a valid one-period instance with immediate check-in. Both products have inventory 100; the single type always chooses product 0 when offered. An optimal normalized LP assignment splits offer probability equally between $\{0\}$ and $\{0,1\}$ and allocates product 0 with unconditional probability $1/2$ on each offer. Its LP value is 1, while Algorithm 5, with its printed unconditional target, earns
--   $$\mathbb E[\mathrm{Rev}_5]=(1-\gamma)/2\le1/2\quad(0\le\gamma\le1).$$
--   A minimizer $\gamma^*(100)$ exists. For every such minimizer the revenue is strictly less than the claimed $(1-\varepsilon^*(100))$ times the LP value. Indeed, evaluating (1) at $\gamma=1/4$ gives $1-\varepsilon^*(100)\ge\frac34(1-e^{-25/7})>1/2$.
--
--   This is a companion refutation of Theorem EC.3; it is not used in the proof of the mission's published goal. It retains the source algorithm exactly in a corner where booking-time conventions and the LP's general index errors disappear.
--
--   **Formalization Note** No general corrected booking theorem is asserted; the refutation uses Algorithm 5 line 9 exactly as printed.
--
--   Differences from the source:
--   - correction: Theorem EC.3 claims a 1 − ε*(c_min) guarantee for Algorithm 5 using an optimal advanced-booking LP assignment. → A normalized optimal assignment with T=t=s_t=1, two inventory-100 products and LP value 1 has Algorithm 5 revenue (1−γ)/2 for every γ in [0,1]; every minimizer γ*(100) violates the printed guarantee.; reason: Algorithm 5 line 9 uses the unconditional y target after already sampling with probability x; the missing division by x introduces a second factor of x. The one-period counterexample satisfies every source assumption and is independent of the unresolved general booking indices.
--   - encoding: The general advanced-booking model has arbitrary times, check-ins, types and rental durations. → The counterexample uses the one-period immediate-check-in restriction and explicitly asserts model assumptions, optimality, normalization, LP value, revenue and existence of a minimizer.; reason: One admissible instance refutes a universal guarantee; this is a refutation, not a weaker corrected theorem.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec27 (PDF 53), Theorem EC.3 and Algorithm 5; LP p. ec26 (PDF 52)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_AdvBookingCounterexample

namespace ReusableAssort.Hybrid.Supplement

/-- Refutation of Theorem EC.3 with Algorithm 5 as printed: the second factor of x
in the unconditional target y cuts revenue in half on an optimal normalized LP assignment. -/
theorem theorem_EC_3_refuted :
    advCounterI.Assumptions ∧ cmin advCounterI = 100 ∧
    advOneOptimal advCounterI advCounterX advCounterY ∧
    (∑ S ∈ advCounterI.feas, advCounterX S) = 1 ∧
    advOneObj advCounterI advCounterY = 1 ∧
    (∀ γ ∈ Set.Icc (0 : ℝ) 1,
      expRevAlg5One advCounterI advCounterX advCounterY γ = (1 - γ) / 2) ∧
    (∃ γ, IsGammaStar 100 γ) ∧
    (∀ γ, IsGammaStar 100 γ →
      expRevAlg5One advCounterI advCounterX advCounterY γ <
        (1 - epsStar 100) * advOneObj advCounterI advCounterY) := by sorry

end ReusableAssort.Hybrid.Supplement

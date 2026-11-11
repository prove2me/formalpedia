-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_comparison_independent_bits
-- name    : QuantumTriangleFinding.Search.comparison_independent_bits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:05.002225+00:00
-- url     : https://prove2.me/theorems/7ce9b53b-4f69-4565-9336-4c304f1f2921
-- title:
--   Lemma 5.2 — Comparison with independent bits
-- statement:
--   Let $I$ be finite, $0<p<1$, and let $\Omega\subseteq\{0,1\}^I$ be nonempty and downward closed. Write $\nu=\mathrm{Bernoulli}(p)^{\otimes I}$ and $\mu=\nu(\cdot\mid\Omega)$. There is a joint probability mass function $\pi(x,y)$ whose marginals are $\mu$ and $\nu$, supported on $x\le y$ coordinatewise. Consequently, every increasing event $A$ satisfies
--   $$\mu(A)\le\nu(A).$$
--   This retains both the monotone coupling and its event-probability consequence. Conditioning has positive probability because downward closure includes the zero input.
--
--   Differences from the source:
--   - generalization: the Section 5 density range 0 < p ≤ 1/(10√Δ) → any 0 < p < 1; reason: the coupling proof uses only a Bernoulli parameter strictly between zero and one; every Section 5 instance lies in this range
--   - encoding: a coupling of random variables (X,Y) → its joint finite probability mass function with the two prescribed marginals and coordinatewise monotone support; reason: a finite joint law and a finite coupling are equivalent
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 5.2, p. 26

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 5.2, p.26: the coupling and increasing-event domination, for all 0<p<1. -/
theorem comparison_independent_bits {I : Type} [Fintype I] (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (Ω : Set (I → Bool))
    (hne : Ω.Nonempty) (hdown : DownwardClosed Ω) :
    ∃ π : ((I → Bool) × (I → Bool)) → ℝ,
      IsProbability π ∧
      (∀ x, ∑ y, π (x, y) = condition (bernoulli p) Ω x) ∧
      (∀ y, ∑ x, π (x, y) = bernoulli p y) ∧
      (∀ x y, 0 < π (x, y) → BitsLE x y) ∧
      (∀ A : Set (I → Bool), Increasing A →
        eventProb (condition (bernoulli p) Ω) A ≤ eventProb (bernoulli p) A) := by sorry

end QuantumTriangleFinding.Search

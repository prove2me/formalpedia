-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_lemma_1
-- name    : WeakEpsNets.LowerBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:47.639954+00:00
-- url     : https://prove2.me/theorems/63e4fe2f-760b-499c-ba78-fc73577292fe
-- title:
--   Lemma 1 — five shifted-square values force a quadratic square
-- statement:
--   Let $q\ge2$ be an even integer, with $\tau=1/(9q^5)$ as in §2.2. Let $G\in\mathbb R[t]$ have degree exactly two. If there are at least five distinct pairs $(a,b)\in[q]\times[q^2]$ satisfying $G(a)=(b+\tau)^2$, then
--   $$\exists\alpha,t_0\in\mathbb R,\qquad G(t)=\alpha(t-t_0)^2\quad\text{as polynomials}.$$
--   This rigidity lemma is the arithmetic input to the replacement argument. The evenness and lower bound on $q$ are the section's standing assumptions, rather than new restrictions.
--
--   Differences from the source:
--   - encoding: five distinct positive integer grid pairs and a degree-two real polynomial → a finite set of natural-number pairs of cardinality at least five, contained in the positive intervals, with natural degree exactly two and a polynomial identity; reason: the source bounds force the integers to be positive; finite sets enforce distinctness and degree two excludes the zero polynomial
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Lemma 1, p. 8, lines 235–236; standing assumptions p. 7, lines 219–221; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Parameters

namespace WeakEpsNets.LowerBound

/-- Lemma 1, source p. 8, with the standing even q ≥ 2 of §2.2. -/
theorem lemma_1 (q : ℕ) (hq : 2 ≤ q) (heven : Even q)
    (G : Polynomial ℝ) (hdegree : G.natDegree = 2)
    (pairs : Finset (ℕ × ℕ))
    (hgrid : pairs ⊆ (positiveInterval q).product (positiveInterval (q ^ 2)))
    (hfive : 5 ≤ pairs.card)
    (hvalues : ∀ ab ∈ pairs, G.eval (ab.1 : ℝ) = ((ab.2 : ℝ) + tau q) ^ 2) :
    ∃ α t₀ : ℝ, G = Polynomial.C α * (Polynomial.X - Polynomial.C t₀) ^ 2 := by sorry

end WeakEpsNets.LowerBound

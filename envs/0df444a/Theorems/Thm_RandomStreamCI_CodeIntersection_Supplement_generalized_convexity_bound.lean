-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_generalized_convexity_bound
-- name    : RandomStreamCI.CodeIntersection.Supplement.generalized_convexity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:49:25.952575+00:00
-- url     : https://prove2.me/theorems/9754dded-9056-4ca2-ae24-2d858e896d6a
-- title:
--   Lemma 24 (used in the proof of Theorem 27) — Generalized convexity bound
-- statement:
--   For a finite code $C\subseteq\Sigma^n$ and a complete-stream branching program $B$, fix $0<\eta<1/2$, $1\le\tau\le n$, and any positive-integer-valued $\kappa$ on $\{0,\ldots,n\}$. At each incoming layer $1\le t\le M=n|\Sigma|$,
--   $$\Phi^{(\tau)}(t)\le\Psi^{(\tau)}(t).$$
--   No terminal admissibility or increment condition on $\kappa$ is imposed. The result controls the vertex potential by its incoming-edge counterpart for Theorem 27.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: the infinite threshold sum in (79)/(88) and integer binomial arguments → the finite range kappa(k_c) <= j <= min(k_c,tau), with signed integer tau-j and beta zero off its support; reason: all omitted terms vanish for positive eta, including on unreachable events
--   - encoding: kappa on {0,...,n} with positive integer values → a total natural function positive only on its used domain; (78) is a separate predicate; reason: values outside the finite domain are never read
--   - generalization: the subsection uses the Reed–Solomon code of OPI → every finite code C and its complete-stream branching program; reason: the displayed convexity assertion and its proof depend only on merging conditional probabilities with fixed nonnegative binomial weights; Reed–Solomon codes specialize directly
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 24, p. 19 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Potential

namespace RandomStreamCI.CodeIntersection.Supplement

/-- Lemma 24, p. 19: positivity of kappa only; (78) is not assumed. -/
theorem generalized_convexity_bound {n w : ℕ} {Alphabet : Type*}
    [Fintype Alphabet] [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (η : ℝ) (κ : ℕ → ℕ) (τ : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1/2) (hτ0 : 1 ≤ τ) (hτn : τ ≤ n)
    (hκ : PositiveThreshold n κ) (t : Fin (Fintype.card (Address n Alphabet))) :
    vertexPotential B C η κ τ (t.val + 1) ≤ edgePotential B C η κ τ t := by sorry

end RandomStreamCI.CodeIntersection.Supplement

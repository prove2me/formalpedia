-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_generalized_potential_bounds_success
-- name    : RandomStreamCI.CodeIntersection.Supplement.generalized_potential_bounds_success
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:48:09.003323+00:00
-- url     : https://prove2.me/theorems/0b508f9d-655d-48cd-af3b-e8bf3f7f9461
-- title:
--   Lemma 23 (used in the proof of Theorem 27) — Generalized potential bounds OPI success
-- statement:
--   Fix a finite code $C\subseteq\Sigma^n$, a branching program $B$ on the complete Boolean oracle stream, $0<\eta<1/2$, and $1\le\tau\le n$. Let $\kappa:\{0,\ldots,n\}\to\mathbb Z_{\ge1}$ satisfy $\kappa(n)\le\tau$ and increments in $\{0,1\}$. With $M=n|\Sigma|$,
--   $$\Phi^{(\tau)}(0)=0,\qquad\Pr[B\text{ succeeds at threshold }\tau]\le2\eta+\Phi^{(\tau)}(M).$$
--   Both assertions use the actual uniform oracle/order law and actual posteriors. This is the terminal conversion from the generalized potential to OPI success, supporting Theorem 27.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: the infinite threshold sum in (79)/(88) and integer binomial arguments → the finite range kappa(k_c) <= j <= min(k_c,tau), with signed integer tau-j and beta zero off its support; reason: all omitted terms vanish for positive eta, including on unreachable events
--   - encoding: kappa on {0,...,n} with positive integer values → a total natural function positive only on its used domain; (78) is a separate predicate; reason: values outside the finite domain are never read
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 23, p. 18 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Potential

namespace RandomStreamCI.CodeIntersection.Supplement

/-- Lemma 23, p. 18: both the zero initial value and the full terminal success bound. -/
theorem generalized_potential_bounds_success {n w : ℕ} {Alphabet : Type*}
    [Fintype Alphabet] [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (η : ℝ) (κ : ℕ → ℕ) (τ : ℕ)
    (hη0 : 0 < η) (hη1 : η < 1/2) (hτ0 : 1 ≤ τ) (hτn : τ ≤ n)
    (hκ : AdmissibleThreshold n τ κ) :
    vertexPotential B C η κ τ 0 = 0 ∧
      tauSuccess B C τ ≤ 2 * η + vertexPotential B C η κ τ (Fintype.card (Address n Alphabet)) := by sorry

end RandomStreamCI.CodeIntersection.Supplement

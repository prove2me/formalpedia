-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_generalized_potential_growth
-- name    : RandomStreamCI.CodeIntersection.Supplement.generalized_potential_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:51:22.263768+00:00
-- url     : https://prove2.me/theorems/9de81d88-76c7-4598-96d8-fe1c3894daee
-- title:
--   Lemma 26 (used in the proof of Theorem 27) — Exact generalized potential growth
-- statement:
--   Let $1\le d\le n$, and let $C\subseteq\Sigma^n$ be a finite code with pairwise agreement at most $d-1$. Fix $s\ge3\sqrt n$, $\eta=e^{-s^2/(4n)}<1/2$, $\kappa(k)=\lceil k/2+s\rceil+1$, and $1\le\tau\le n$. For an arbitrary positive-width $w$ branching program $B$, writing $S=\log_2 w$, with
--   $$\log_2 w\le\frac{s^2}{8d}-\log_2|C|,$$
--   at every $0\le t<M=n|\Sigma|$,
--   $$\Psi^{(\tau)}(t+1)-\Phi^{(\tau)}(t)\le\frac{n/(d\eta)+1}{M-t}\max_{0\le k<n}\left(\frac{n-k}{2}\beta_{n-k-1}(\tau-\kappa(k))\right).$$
--   The binomial argument is signed; the threshold ceiling, the additive one, the factor $(n-k)/2$ and the full maximum are retained. No condition $\kappa(n)\le\tau$ is assumed. This is the one-step estimate supporting Theorem 27.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: the infinite threshold sum in (79)/(88) and integer binomial arguments → the finite range kappa(k_c) <= j <= min(k_c,tau), with signed integer tau-j and beta zero off its support; reason: all omitted terms vanish for positive eta, including on unreachable events
--   - encoding: the maximum over 0 <= k < n and width w=2^S → the supremum of a finite nonempty real image and arbitrary natural width w with budget log_2 w; reason: d>=1 and d<=n ensure an attained maximum; t<M ensures a positive denominator; B.start forces w>0, so S=log_2 w is exactly equivalent to w=2^S without rounding
--   - generalization: log_2 |C| implicitly requires a nonempty code → also permits C empty, using the published total value log_2 0=0; reason: all source nonempty codes are included; for the added empty case both potentials are zero and the right side is nonnegative
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 26, p. 20 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Agreement
import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Potential

namespace RandomStreamCI.CodeIntersection.Supplement

/-- Lemma 26, p. 20, proof through p. 22: exact one-step growth, with all constants.
The width is arbitrary, with S = log₂ w as in the source's w = 2^S.
No terminal-threshold admissibility assumption is added. -/
theorem generalized_potential_growth {n d w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (hd0 : 1 ≤ d) (hdn : d ≤ n) (C : Finset (Word n Alphabet))
    (hC : PairwiseAgreement C d) (s : ℝ)
    (hs : 3 * Real.sqrt (n : ℝ) ≤ s) (hη : surplusEta n s < 1/2)
    (B : BranchingProgram n Alphabet w) (τ : ℕ) (hτ0 : 1 ≤ τ) (hτn : τ ≤ n)
    (hS : log₂ (w : ℝ) ≤ s^2 / (8 * (d : ℝ)) - log₂ (C.card : ℝ))
    (t : Fin (Fintype.card (Address n Alphabet))) :
    edgePotential B C (surplusEta n s) (surplusThreshold s) τ t -
        vertexPotential B C (surplusEta n s) (surplusThreshold s) τ t.val ≤
      (((n : ℝ) / ((d : ℝ) * surplusEta n s) + 1) /
        ((Fintype.card (Address n Alphabet) : ℝ) - t.val)) *
        growthMaximum n τ (surplusThreshold s) := by sorry

end RandomStreamCI.CodeIntersection.Supplement

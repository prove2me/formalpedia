-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_conditional_min_entropy
-- name    : RandomStreamCI.CodeIntersection.conditional_min_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:18.020327+00:00
-- url     : https://prove2.me/theorems/8e98bdbb-812c-4aec-b5b1-db7b064d200d
-- title:
--   Proposition 9 — Conditional entropy after bounded-memory computation
-- statement:
--   Fix a classical program of width $w=2^S$ (so $S=\log_2 w$), time $0\le t\le M$, and observed address set $A$ of size $t$. For every $\varepsilon>0$, the vertices of positive conditional mass where the following bound fails have total mass at most $\varepsilon$, conditioned on $A_t=A$:
--
--   $$H_\infty(H_A\mid E_{v,A})\ge t-\log_2 w-\log_2(1/\varepsilon).$$
--
--   Unreachable vertices have zero contribution and are excluded from the entropy test. The statement controls exceptional probability mass rather than average entropy, supplying the information loss estimate used in the potential bound.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: program of width w = 2^S, with the bound t − S − log(1/ε) → program of arbitrary width w (states Fin w), with S replaced by log₂ w; reason: S = log₂ w is the source's own relation; every source program (any width, integer or not S) is an instance and nothing else is added
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Proposition 9, printed p. 9 / PDF p. 9

import Definitions.Def_RandomStreamCI_CodeIntersection_Branching

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 9, p. 9 (16), for a program of width w = 2^S, i.e. S = log₂ w.
Bad positive-mass vertices have conditional total mass at most epsilon. -/
theorem conditional_min_entropy {n w : ℕ} {Alphabet : Type} [Fintype Alphabet]
    [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (t : ℕ) (ht : t ≤ Fintype.card (Address n Alphabet))
    (A : Finset (Address n Alphabet)) (hA : A.card = t) (ε : ℝ) (hε : 0 < ε) :
    (∑ v : Fin w,
      if 0 < streamProbability (B.vertexEvent t v A) ∧
          minEntropy (B.restrictedPosterior t v A) < (t : ℝ) - log₂ w - log₂ (1 / ε)
      then streamProbability (B.vertexEvent t v A) else 0) /
      streamProbability (fun ω => seen ω.2 t = A) ≤ ε := by sorry

end RandomStreamCI.CodeIntersection

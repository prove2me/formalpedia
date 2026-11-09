-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_8
-- name    : RankingQueryCost.Joint.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:26:47.560201+00:00
-- url     : https://prove2.me/theorems/4163ce21-f733-4640-9940-1454173267e8
-- title:
--   Lemma 4.8 — Lower bound for forced completion
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   For every sound forced-completion protocol that succeeds with probability at least $3/4$ in every clean world, its hard distinct-identity budget $B$ obeys, for one absolute $c>0$,
--
--   $$B\ge c\min\{N,n\log n+ns\}.$$
--
--   Protocols may randomize and may refuse on unsuccessful paths. Every released completion must retain acquired replies and fill only orientations forced by the supplied budget. This is the optimality lower bound, not an assumption on an upper construction.
--
--   **Formalization Note** The lower-bound and operational-infimum classes also permit divergent private paths, which never contribute to success. This enlarges those classes and strengthens the lower claim. Every constructed upper implementation must return on every tape, so all original every-path output, safety and refusal guarantees are retained.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - generalization: the source query tasks with returned real estimates and hard identity budgets → a larger measurable private-tape protocol class whose divergent paths count as failures, with every finite upper witness required to halt on all tapes; reason: the source lower-bound arguments still apply when divergence is failure; each source protocol is included, and the explicit always-halting finite upper witnesses recover the original actual, every-path safe and dual guarantees
--   - encoding: O, Omega or Theta comparison with the stated parameter dependence → positive comparison constants quantified before every instance parameter and a finite operational optimum where applicable; reason: this spells out the same asymptotic contract without selecting a numeric universal comparison constant
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.8, p. 22, PDF p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Completion

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.8, p. 22 / PDF 23, with one absolute lower comparison constant. -/
theorem lemma_4_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ n s B : ℕ, Admissible n s →
      ∀ A : QueryPolicy n, HardBudget s 0 B A →
        SoundForcedPolicy s 0 A → CleanCompletionSuccess A →
        c * min (pairCount n : ℝ) ((n : ℝ) * Real.log n + n * s) ≤ (B : ℝ) := by sorry

end RankingQueryCost.Joint

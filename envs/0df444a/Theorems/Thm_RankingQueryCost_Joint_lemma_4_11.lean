-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_11
-- name    : RankingQueryCost.Joint.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:59.554585+00:00
-- url     : https://prove2.me/theorems/c0dae541-8b85-423f-a438-efde6bec749e
-- title:
--   Lemma 4.11 — Online relocation
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   For $s\ge1$ and $0<\varepsilon\le\varepsilon_0$, every causal randomized protocol attaining actual $\varepsilon$-accuracy against up to $s$ online faulty identities has hard budget
--
--   $$B\ge c\min\{ns,s/\varepsilon\}$$
--
--   for one absolute $c>0$. The true rank is fixed before the private seed; only fault designations occur online. The bound allows every continuous estimate in $Q$.
--
--   **Formalization Note** The lower-bound and operational-infimum classes also permit divergent private paths, which never contribute to success. This enlarges those classes and strengthens the lower claim. Every constructed upper implementation must return on every tape, so all original every-path output, safety and refusal guarantees are retained.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - generalization: the source query tasks with returned real estimates and hard identity budgets → a larger measurable private-tape protocol class whose divergent paths count as failures, with every finite upper witness required to halt on all tapes; reason: the source lower-bound arguments still apply when divergence is failure; each source protocol is included, and the explicit always-halting finite upper witnesses recover the original actual, every-path safe and dual guarantees
--   - encoding: O, Omega or Theta comparison with the stated parameter dependence → positive comparison constants quantified before every instance parameter and a finite operational optimum where applicable; reason: this spells out the same asymptotic contract without selecting a numeric universal comparison constant
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.11, p. 24, PDF p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.11, p. 24 / PDF 25. All faulty identities may be selected online. -/
theorem lemma_4_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n s B : ℕ) (ε : ℝ),
      Admissible n s → 1 ≤ s → 0 < ε → ε ≤ precisionCeiling →
      ∀ A : QueryPolicy n, HardBudget 0 s B A → Actual 0 s ε A →
        c * min ((n : ℝ) * s) ((s : ℝ) / ε) ≤ (B : ℝ) := by sorry

end RankingQueryCost.Joint

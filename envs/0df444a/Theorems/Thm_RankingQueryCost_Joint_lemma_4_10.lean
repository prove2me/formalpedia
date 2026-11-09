-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_10
-- name    : RankingQueryCost.Joint.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:53.331193+00:00
-- url     : https://prove2.me/theorems/59aa14e8-7958-4e0c-9183-466cf39a2b14
-- title:
--   Lemma 4.10 — Relocation
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Let $0<\tau\le\varepsilon_0$. A sound public $\tau$-certificate protocol with strictly positive emission probability in every clean world must have hard identity budget
--
--   $$B\ge c\min\{ns,s/\tau\}$$
--
--   for one absolute $c>0$. Actual accuracy is not assumed, and emission need not have a fixed positive lower probability. Every released estimate is in $Q$ and its accepted verifier decision certifies all orders compatible with the supplied budget. This is the public-information lower bound.
--
--   **Formalization Note** The lower-bound and operational-infimum classes also permit divergent private paths, which never contribute to success. This enlarges those classes and strengthens the lower claim. Every constructed upper implementation must return on every tape, so all original every-path output, safety and refusal guarantees are retained.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - generalization: the source query tasks with returned real estimates and hard identity budgets → a larger measurable private-tape protocol class whose divergent paths count as failures, with every finite upper witness required to halt on all tapes; reason: the source lower-bound arguments still apply when divergence is failure; each source protocol is included, and the explicit always-halting finite upper witnesses recover the original actual, every-path safe and dual guarantees
--   - encoding: O, Omega or Theta comparison with the stated parameter dependence → positive comparison constants quantified before every instance parameter and a finite operational optimum where applicable; reason: this spells out the same asymptotic contract without selecting a numeric universal comparison constant
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.10, p. 23, PDF p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.10, p. 23 / PDF 24. No actual accuracy or constant emission probability is
assumed: strictly positive emission in each clean order is enough. -/
theorem lemma_4_10 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n s B : ℕ) (τ : ℝ),
      Admissible n s → 0 < τ → τ ≤ precisionCeiling →
      ∀ (A : QueryPolicy n) (V : PublicVerifier n),
        HardBudget s 0 B A → VerifierSound s τ V →
        (∀ W, LegalWorld s W → ∀ ω o, Returns A W 0 ω o → o.emission = true →
          o.estimate ∈ estimateSet n ∧ V o.state.ledger o.estimate o.certificate = true) →
        (∀ W : ComparisonWorld n, W.initial = ∅ →
          0 < privateLaw {ω | ∃ o, Returns A W 0 ω o ∧ o.emission = true}) →
        c * min ((n : ℝ) * s) ((s : ℝ) / τ) ≤ (B : ℝ) := by sorry

end RankingQueryCost.Joint

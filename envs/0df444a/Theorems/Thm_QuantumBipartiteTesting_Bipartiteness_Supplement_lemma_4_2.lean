-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_2
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:55.385956+00:00
-- url     : https://prove2.me/theorems/228ed4f5-0754-4114-ad38-7b673ad39f18
-- title:
--   Lemma 4.2 — Intermediate random matching cut expansion
-- statement:
--   Let $H$ follow the feasible unsigned matching law on $n$ visible vertices at $(M_0,1)$, with an even number $c\ge400\ln n$ of colors. For all sufficiently large $n$, the probability that some cut fails the inequality $|e_H(U,U^c)|\ge(c/20)|U|$ for $|U|\le n/2$ is at most
--   $$B(n,c)=\sum_{u=1}^{\lfloor n/2\rfloor}\binom nu\exp(-cu/80).$$
--   For every $\delta>0$, eventually $B(n,c)\le\delta$, uniformly over these color counts. The all-cuts minimum formulation is equivalent by taking complements. This supplies simultaneous expansion of the intermediate YES graph.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - generalization: c is an even logarithmic color count with sufficiently large coefficient → all even c at least 400 ln n, without an upper logarithmic bound; reason: the cut-failure sum and replacement promises improve with more independent matching colors; the logarithmic regime is included
--   - encoding: with probability 1-o(1) → the explicit A.7 failure sum and its uniform vanishing; reason: A.7 p.38 gives this bound; complement symmetry gives the all-cuts minimum formulation
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.2, printed page = PDF page 22; proof pp.37–38

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_2 :
    (∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ c : ℕ,
      Even c → 400 * Real.log n ≤ (c : ℝ) →
      1 - FeasibleProb n (Center n) 1 c (ColoredExpansion (1/20)) ≤ CutFailureBound n c) ∧
    (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ c : ℕ,
      Even c → 400 * Real.log n ≤ (c : ℝ) → CutFailureBound n c ≤ δ) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement

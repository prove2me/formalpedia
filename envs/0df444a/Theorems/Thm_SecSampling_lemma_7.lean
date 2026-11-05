-- Prove2me | Theorems.Thm_SecSampling_lemma_7
-- name    : SecSampling.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:52.609205+00:00
-- url     : https://prove2.me/theorems/47c13d47-2d38-48e6-aa2e-72d9b95447cd
-- title:
--   Lemma 7 — no deterministic algorithm wins two conflicting instances
-- statement:
--   In the last zero problem, let $q$ be a **deterministic** strategy, i.e. one whose stopping decision $q(m,h)$ is always $0$ or $1$. If the instances $I_1$ and $I_2$ are in conflict, then $q$ does not win in both of them.
--
--   This is the basic constraint behind the conflict graph: a deterministic strategy selects at most one node of each conflicting pair.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm wins in an instance → a strategy with values in {0, 1} whose winning probability on the instance is 1; reason: a deterministic strategy wins with probability 0 or 1
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 7, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace SecSampling

/-- **Lemma 7** (arXiv:2011.07869v1, p.15). No deterministic algorithm can win in two conflicting
instances: if a last-zero strategy `q` only takes the values `0` and `1`, and `I₁`, `I₂` are in
conflict, then `q` does not win (with probability one) in both. -/
theorem lemma_7 (q : LZStrategy) (hq : ∀ (m : ℕ) (h : List Bool), q m h = 0 ∨ q m h = 1)
    (I₁ I₂ : List Bool) (h : Conflict I₁ I₂) :
    ¬ (winLZ q I₁ = 1 ∧ winLZ q I₂ = 1) := by sorry

end SecSampling

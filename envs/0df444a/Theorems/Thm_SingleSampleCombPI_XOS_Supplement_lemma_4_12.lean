-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_4_12
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:34.026747+00:00
-- url     : https://prove2.me/theorems/016ba179-dd75-4040-b848-3cc3a08a0899
-- title:
--   Lemma 4.12 — Existence of the implicit post-update fixed point
-- statement:
--   For every reachable Algorithm 6 state before the next allocation and every normalized monotone twice-differentiable concave DR-submodular arriving valuation on the nonnegative orthant, there exists $x\in[0,1]^m$ satisfying
--   $$x\in\arg\max_{y\in[0,1]^m}\{v(y)-\langle y,p(x)\rangle\}.$$
--   Here $p(x)$ is the hypothetical post-update dual vector obtained by allocating $x$ with its Aumann–Shapley supporting prices. Existence is the conclusion, not an assumed field of a valid state.
--
--   Differences from the source:
--   - encoding: twice-differentiable DR-submodular concave valuations on the nonnegative orthant and Algorithm 6 → within-orthant first/second Frechet derivatives, antitone gradient, canonical Aumann–Shapley prices and reachable frozen-history transitions; reason: these are Definition 6 and Proposition 2.2 conventions; C² regularity, Lipschitz constants and arbitrary supplied supporting maps are not assumed
--   - encoding: valid states, traces and arbitrary arrival order → inductively reachable histories and explicit order-indexed frozen records; reason: only initialization and actual Condition 1 transitions are assumed; no lemma conclusion or unproved algorithmic invariant is a state field
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 4.12, printed p. 26 / PDF p. 28; proof printed 26–27 / PDF 28–29.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 4.12, PDF 28 / printed 26. Existence in every reachable
state, using the post-update prices and canonical supporting map. -/
theorem lemma_4_12 {m : ℕ} (H : FrozenHistory m) (hH : A6Reachable H)
    (v : Vec m → ℝ) (hv : DRConcave v) :
    ∃ x : Cube m, condition1 H v x := by sorry

end SingleSampleCombPI.XOS.Supplement

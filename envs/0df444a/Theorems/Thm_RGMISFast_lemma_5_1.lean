-- Prove2me | Theorems.Thm_RGMISFast_lemma_5_1
-- name    : RGMISFast.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:46.725023+00:00
-- url     : https://prove2.me/theorems/5075a072-32fa-41a1-a8f3-bb62f8cdd6a9
-- title:
--   Lemma 5.1: average neighborhood size of attached sets, $\frac1{|S|}\sum_{W\in S}d(W)\ge\frac ke|S|^{1/k}$
-- statement:
--   Let $H$ be a finite graph containing $u^*$, let $k\ge1$, and let $S$ be a nonempty family of distinct $k$-sets attached to the root. Then
--   $$
--   \frac1{|S|}\sum_{W\in S}d(W)\ge\frac ke\,|S|^{1/k}, \tag{18}
--   $$
--   where $d(W)$ counts the vertices of $W$ together with all vertices adjacent to $W$ or to $u^*$, not counting $u^*$.
--
--   Many attached sets force a large average neighbourhood; this is the deterministic input of Lemma 5.2.
--
--   **Formalization Note** $S$ is a finite family of vertex sets, each of size $k$ and attached to $\{u^*\}$ (so it avoids $u^*$); $|S|^{1/k}$ is the real power.
--
--   Differences from the source: none.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 5.1, eq. (18), p.17 (PDF p.19); proof in §5.3, pp.21–22

import Mathlib
import Definitions.Def_RGMISFast_IsRootConnected

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 5.1 (Average Neighborhood Size of Attached Sets; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.17, proof in §5.3): let `H` be a
finite graph containing `u∗`, let `k ≥ 1`, and let `S` be a nonempty family of distinct `k`-sets
attached to the root. Then `(1/|S|) Σ_{W∈S} d(W) ≥ (k/e) |S|^{1/k}` (18).

**Formalization Note** `H` is a simple graph on a finite vertex type containing `u`; `S` is a
finset of finsets (so its members are distinct), each of size `k` and attached to `{u}` (in
particular not containing `u`). `|S|^{1/k}` is the real power. Deterministic: no ranks. -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (k : ℕ)
    (hk : 1 ≤ k) (S : Finset (Finset V)) (hS : S.Nonempty)
    (hSk : ∀ W ∈ S, W.card = k ∧ IsAttached H {u} W) :
    (k / Real.exp 1) * (S.card : ℝ) ^ (1 / (k : ℝ)) ≤
      (1 / (S.card : ℝ)) * ∑ W ∈ S, (dW H u W : ℝ) := by sorry

end RGMISFast

-- Prove2me | Theorems.Thm_TenChallenges_caccettaHaggkvist_dense
-- name    : TenChallenges.caccettaHaggkvist_dense
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:34:58.081592+00:00
-- url     : https://prove2.me/theorems/1038dee2-668b-4b29-aa2a-de74e859c231
-- title:
--   Caccetta–Häggkvist in the Dense Regime
-- statement:
--   A nonempty finite loopless digraph with minimum outdegree at least r and at most 2r vertices satisfies the Caccetta–Häggkvist cycle bound. In fact it has a directed two-cycle. In particular, this establishes the outdegree-two case for graphs of order at most four.
-- source:
--   Ten Challenges in Combinatorics, Challenge 3; dense-case supporting lemma. https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_03

namespace TenChallenges
theorem caccettaHaggkvist_dense (r : ℕ) {V : Type} [Fintype V] [Nonempty V]
    (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, r ≤ G.outDegree v)
    (hcard : Fintype.card V ≤ 2 * r) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * r < Fintype.card V + r ∧ G.HasCycleOfLength ℓ := by sorry
end TenChallenges

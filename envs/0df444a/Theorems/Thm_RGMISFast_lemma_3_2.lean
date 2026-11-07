-- Prove2me | Theorems.Thm_RGMISFast_lemma_3_2
-- name    : RGMISFast.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:49.239791+00:00
-- url     : https://prove2.me/theorems/e332dbb2-513a-4c7b-80c2-e76823f7cc06
-- title:
--   Lemma 3.2: top component, $|C_0|\le1+L$ w.p. $\ge1-e^{-L}$, and $S_0(T_{a_0})=|V(T_{a_0})|\le1+L$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$ and i.i.d. Exp(1) ranks, and let $L$ be a real number (the source's deviation parameter of §3 has $L\ge8$). With probability at least $1-e^{-L}$,
--   $$
--   |C_0|\le 1+L. \tag{11}
--   $$
--   Conditioned on this event, every admissible tree satisfies
--   $$
--   S_0(T_{a_0})=|V(T_{a_0})|\le 1+L .
--   $$
--
--   This initializes the recurrence of Proposition 4.1 at the top interval $[a_0,\infty)$.
--
--   **Formalization Note** The second clause is deterministic: for every rank vector with distinct nonnegative ranks satisfying (11), and every admissible tree. $L$ is any real number; the source's case is $L\ge8$.
--
--   Differences from the source:
--   - encoding: with probability at least 1 − e^{−L} → the (outer) measure of {|C₀| > 1 + L} is at most e^{−L}; reason: equivalent for a probability measure
--   - encoding: conditioned on this event (ranks distinct, in [0, ∞), standing assumption of §2) → for every injective nonnegative rank vector satisfying (11); reason: a deterministic statement on the event; the standing assumption holds almost surely
--   - generalization: L the deviation parameter of §3, L ≥ 8 (fixed in Lemma 3.1) → every real L; reason: the proof (k = ⌊L⌋ + 1, §6.3) works for every L ≥ 0, the probability bound is trivial for L < 0 (e^{−L} > 1), and the deterministic clause holds for every L since V(T_{a₀}) ⊆ C₀; L ≥ 8 is a special case
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 3.2, eq. (11), p.14 (PDF p.16); proof in §6.3, pp.25–26

import Mathlib
import Definitions.Def_RGMISFast_AdmissibleTree
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 3.2 (Top Component; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.14, proof in §6.3): with probability at least `1 − e^{−L}`,
`|C₀| ≤ 1 + L` (11); conditioned on this event, every admissible tree satisfies
`S₀(T_{a₀}) = |V(T_{a₀})| ≤ 1 + L`.

**Formalization Note** `L` is any real number: §3 fixes the deviation parameter `L ≥ 8` in
Lemma 3.1, and the proof of Lemma 3.2 (`k = ⌊L⌋ + 1`, §6.3) works for every `L ≥ 0`, while for
`L < 0` the bound `e^{−L} > 1` is trivial; the case `L ≥ 8` is the source's. The first clause bounds the
(outer) measure of `{|C₀| > 1 + L}` under the i.i.d. Exp(1) rank law; the second is
deterministic, for every rank vector with distinct nonnegative ranks (standing assumption of §2)
satisfying (11). `T_{a₀}` is `T.prefix (am 0)` (`a_0 = a₀`). No degree bound is involved. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (L : ℝ) :
    rankLaw V {r | ¬ TopEvent G u L r} ≤ ENNReal.ofReal (Real.exp (-L)) ∧
    ∀ r : V → ℝ, Function.Injective r → (∀ v, 0 ≤ r v) → TopEvent G u L r →
      ∀ T : AdmissibleTree G r u,
        Sm r (T.prefix (am 0)) 0 = ((T.prefix (am 0)).card : ℝ) ∧
        ((T.prefix (am 0)).card : ℝ) ≤ 1 + L := by sorry

end RGMISFast

-- Prove2me | Theorems.Thm_RGMISFast_proposition_4_2
-- name    : RGMISFast.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:56.608634+00:00
-- url     : https://prove2.me/theorems/5e69a892-6699-4adc-a247-a5191c8a6f6f
-- title:
--   Proposition 4.2: on $E_h$ every admissible tree has at most $C^*\Delta^{90}(1+h)$ vertices
-- statement:
--   There is an absolute constant $C^*>0$ with the following property. Let $G$ be a finite simple graph with all degrees at most $\Delta\ge2$, root $u^*$, and distinct ranks $r:V\to[0,\infty)$, let $h\ge0$, and suppose the ranks lie in the good event $E_h$ (the conclusions of Lemmas 3.1, 3.2 and A.1 at $L=h+8$). Then every admissible tree $T$ satisfies
--   $$
--   |V(T)|\le C^*\Delta^{90}(1+h).
--   $$
--
--   Combined with Observation 2.2 and eq. (12), this gives the tail bound of Theorem 1.1.
--
--   **Formalization Note** $C^*$ is chosen before the vertex type, the graph and all other data. The statement is deterministic: it holds for every rank vector in $E_h$.
--
--   Differences from the source:
--   - encoding: distinct ranks r : V → [0, ∞), the paper's standing assumption (§1.1, p.2; §2, p.10) → hypotheses `Function.Injective r` and `∀ v, 0 ≤ r v`; reason: the standing assumption written as hypotheses; it holds almost surely
--   - encoding: conditioned on E_h → for every rank vector satisfying `GoodEvent G Δ u (h + 8)`; reason: a deterministic statement on the event, as in the proof
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Proposition 4.2, p.16 (PDF p.18); L = h + 8, p.15

import Mathlib
import Definitions.Def_RGMISFast_AdmissibleTree
import Definitions.Def_RGMISFast_GoodEvent

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Proposition 4.2 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.16): conditioned on `E_h`, every admissible tree has at most
`C∗∆^90(1 + h)` vertices, where `C∗` is an absolute constant.

**Formalization Note** `C∗` is chosen before the graph and all other data. `E_h` is
`GoodEvent G Δ u (h + 8)` (`L = h + 8`, `h ≥ 0`, "Throughout this section, L = h + 8, for an
h ≥ 0", p.15). The statement is deterministic: for every rank vector in `E_h`, with distinct
nonnegative ranks (the standing assumption of §2), all degrees at most `∆`, `∆ ≥ 2`. -/
theorem proposition_4_2 : ∃ Cstar : ℝ, 0 < Cstar ∧
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, G.degree v ≤ Δ) → ∀ (u : V) (h : ℝ), 0 ≤ h →
        ∀ r : V → ℝ, Function.Injective r → (∀ v, 0 ≤ r v) → GoodEvent G Δ u (h + 8) r →
          ∀ T : AdmissibleTree G r u, (T.nodes.card : ℝ) ≤ Cstar * (Δ : ℝ) ^ 90 * (1 + h) := by sorry

end RGMISFast

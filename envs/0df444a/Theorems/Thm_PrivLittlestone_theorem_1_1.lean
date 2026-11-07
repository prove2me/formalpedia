-- Prove2me | Theorems.Thm_PrivLittlestone_theorem_1_1
-- name    : PrivLittlestone.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:02.760781+00:00
-- url     : https://prove2.me/theorems/b97501b3-3ec5-4046-abf4-b22f96677b87
-- title:
--   Theorem 1.1 — every Littlestone class of dimension $d$ has an $(\varepsilon,\delta)$-private online learner with $M_T \le \min\{T, Cd^{3/2}\Lambda_d^{5/2}/\varepsilon\}$ w.p. $1-\beta$
-- statement:
--   Let $C$ be a universal constant. For $T \ge 1$, $0 < \varepsilon \le 1$ and $0 < \delta, \beta \le 1/2$, write
--   $$
--   \Lambda_q = \log\frac{e(q+1)(T+1)}{\varepsilon\delta\beta}.
--   $$
--   For every nonempty binary class $H$ with Littlestone dimension $\mathrm{LDim}(H) = d \ge 1$, there exists an $(\varepsilon, \delta)$-private online learner such that, on every fixed length-$T$ sequence realizable by $H$,
--   $$
--   \mathbb P\left[ M_T \le \min\left\{ T,\ \frac{C d^{3/2} \Lambda_d^{5/2}}{\varepsilon} \right\} \right] \ge 1 - \beta .
--   $$
--   The learner may be improper.
--
--   Privacy holds on all inputs, both under replacement of one record of a fixed stream and in the adaptive single-challenge model. The bound improves the dimension dependence of the previous private oblivious bound from $d^{9.5}$ to $d^{3/2}$.
--
--   **Formalization Note** $C$ is chosen before every other quantifier. $\mathrm{LDim}$ is the published `UnderstandingML.ldim`. The learner releases arbitrary classifiers $X \to \{0,1\}$ (improper) and is regular (probability coins, measurable releases with countably many values).
--
--   Differences from the source:
--
--   - reading: an (ε, δ)-private online learner → (ε, δ)-private both in the adaptive single-challenge model (Definition 2.1) and under replacement on fixed streams (§2.1), on all inputs; reason: the paper uses '(ε, δ)-private' for both notions and proves both (Theorem 4.1, abstract)
--   - generalization: an online learner → a regular online learner (probability coins, measurable releases with countable range); reason: extra conclusion; rules out non-measurable witnesses; the paper's learner is regular
--   - encoding: a universal constant C → ∃ C before all other quantifiers, which may formally depend on the universe level of X; reason: Lean universe polymorphism
--   - encoding: rounds 1, …, T → 0-based rounds; reason: same transcript
--   - encoding: randomized adversaries in Definition 2.1, whose view holds hypotheses, record pairs and coins → deterministic strategies and events on classifier transcripts, all subsets; reason: with the coins fixed the pairs are a function of the released classifiers; per-coin bounds integrate to randomized adversaries (proof of Lemma B.3); regularity makes every subset an event
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Theorem 1.1, p.1

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner_IsRegular
import Definitions.Def_PrivLittlestone_IsAdaptivePrivate
import Definitions.Def_PrivLittlestone_IsReplacementPrivate
import Definitions.Def_PrivLittlestone_mistakes
import Definitions.Def_PrivLittlestone_IsRealizableBy
import Definitions.Def_PrivLittlestone_bigLam
import Definitions.Def_UnderstandingML_Online

universe u

namespace PrivLittlestone

/-- **Theorem 1.1 (Oblivious learning of Littlestone classes)** (He–He, *Private Online Learning
of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Theorem 1.1, p.1). Let `C` be a universal constant. For `T ≥ 1`, `0 < ε ≤ 1` and
`0 < δ, β ≤ 1/2`, write `Λ_q = log(e(q + 1)(T + 1)/(εδβ))`. For every nonempty binary class `H`
with `LDim(H) = d ≥ 1`, there exists an `(ε, δ)`-private online learner such that, on every fixed
length-`T` sequence realizable by `H`, `P[M_T ≤ min{T, C d^{3/2} Λ_d^{5/2}/ε}] ≥ 1 − β`. The learner
may be improper.

**Formalization Note** `C` is chosen before every other quantifier (it may formally depend on
the universe level of `X`). "(ε, δ)-private" is asserted in both senses of the paper, the
adaptive single-challenge model (Definition 2.1) and replacement on fixed streams (§2.1), on all
inputs; the learner is also regular (a probability measure on the coins, measurable releases with
countable range). Classifiers range over all of `X → Bool` (improper). `LDim` is the published
`UnderstandingML.ldim`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (H : Set (X → Bool)) (d : ℕ),
        H.Nonempty → UnderstandingML.ldim H = d → 1 ≤ d →
        ∀ (T : ℕ) (ε δ β : ℝ), 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 → 0 < β → β ≤ 1 / 2 →
          ∃ A : OnlineLearner X, A.IsRegular T ∧
            IsAdaptivePrivate A T ε δ ∧ IsReplacementPrivate A T ε δ ∧
            ∀ z : Fin T → X × Bool, IsRealizableBy H z →
              ENNReal.ofReal (1 - β) ≤ A.μ {ω |
                (mistakes A z ω : ℝ) ≤
                  min (T : ℝ) (C * (d : ℝ) ^ (3 / 2 : ℝ) * (bigLam d T ε δ β) ^ (5 / 2 : ℝ) / ε)} := by sorry

end PrivLittlestone

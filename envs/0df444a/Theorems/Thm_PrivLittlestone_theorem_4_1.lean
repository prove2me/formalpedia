-- Prove2me | Theorems.Thm_PrivLittlestone_theorem_4_1
-- name    : PrivLittlestone.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:48:36.364662+00:00
-- url     : https://prove2.me/theorems/15a41ead-31f8-4335-871a-13503a11ffba
-- title:
--   Theorem 4.1 — Algorithm 1 is $(\varepsilon,\delta)$-private on all inputs and makes $M_T \le \min\{T, 2KU\}$ mistakes under (A1)–(A2)
-- statement:
--   Fix a ranked candidate system of height $D$ and branching parameter $B$, a public aggregation rule, a deterministic training filter and a fallback classifier, all defined on arbitrary inputs. Let $K, m, T \ge 1$, $0 < \varepsilon \le 1$ and $0 < \delta, \beta \le 1/2$, use the parameters (4)–(7) and require the cap condition (8)
--   $$
--   K > 20(L_0 + aD + 1), \qquad L_0 = \log|C(\emptyset)| .
--   $$
--   Then Algorithm 1:
--
--   1. is a regular online learner (probability coins, measurable releases with countably many values);
--   2. is $(\varepsilon, \delta)$-private in the adaptive single-challenge model on all inputs, and hence $(\varepsilon,\delta)$-private under replacement on fixed streams;
--   3. on every input strategy satisfying (A1) and (A2), with probability at least $1 - \beta$,
--   $$
--   M_T \le \min\{T, 2KU\}. \tag{9}
--   $$
--
--   This is the general continual learner of the paper: any ranked candidate system with a certified aggregation rule yields a private online learner whose number of mistakes is the number of phases times the per-phase threshold.
--
--   **Formalization Note** The learner is `continualLearner` with $\eta = \varepsilon_s/4$, $a = \eta + \log(8B/\tau)$, $U = \lceil 96/\varepsilon_s + 16L_T/\varepsilon_a\rceil$, $\varepsilon_a = \varepsilon/2$. Input strategies are deterministic and see the current classifier.
--
--   Differences from the source:
--
--   - generalization: an admissible realizable input family I on which (A1)–(A2) hold → every input strategy satisfying (A1) and (A2), realizable or not; reason: the proof uses only (A1) and (A2); realizable families are sets of such strategies
--   - generalization: Algorithm 1 is (ε, δ)-private in the adaptive single-challenge model → also regular, and also (ε, δ)-private under replacement on fixed streams; reason: extra conclusions; replacement privacy follows from the adaptive clause through the constant adversary (proved in the sanity file)
--   - reading: (A1) every mistake returns a record and the retained sequence is covered; (A2) except with conditional probability β/(4K) at a phase's sampling step, every mistake on the relevant future inputs is certified → (A1) for almost every run, on rounds before the fallback; (A2) for almost every history, at every phase start, over the phase's samples, on the continuation with the aggregate held fixed; reason: pins down 'conditional probability' and 'relevant future inputs'; each actual phase is a prefix of the continuation
--   - encoding: randomized adaptive inputs and adversaries → deterministic strategies (fixed coins); reason: randomized ones are mixtures; the bounds integrate
--   - encoding: rounds 1, …, T and fresh randomness → 0-based rounds and an explicit product coin space; reason: same algorithm
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Theorem 4.1, (9), p.8

import Mathlib
import Definitions.Def_PrivLittlestone_continualLearner
import Definitions.Def_PrivLittlestone_OnlineLearner_IsRegular
import Definitions.Def_PrivLittlestone_IsAdaptivePrivate
import Definitions.Def_PrivLittlestone_IsReplacementPrivate
import Definitions.Def_PrivLittlestone_IsA1
import Definitions.Def_PrivLittlestone_IsA2
import Definitions.Def_PrivLittlestone_gameMistakes
import Definitions.Def_PrivLittlestone_aP
import Definitions.Def_PrivLittlestone_Uth

namespace PrivLittlestone

/-- **Theorem 4.1 (Continual structural learning)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Theorem 4.1, p.8). Fix a ranked candidate system of height `D` and branching
parameter `B`, a public aggregation rule, a deterministic training filter and a fallback
classifier. For `K, m, T ≥ 1`, `0 < ε ≤ 1`, `0 < δ, β ≤ 1/2`, run Algorithm 1 with the parameters
(4)–(7) (`η = ε_s/4`, `a = η + log(8B/τ)`, `U = ⌈96/ε_s + 16L_T/ε_a⌉`, `ε_a = ε/2`) under the cap
condition (8) `K > 20(L₀ + aD + 1)`, `L₀ = log |C(∅)|`. Then Algorithm 1 is a regular online
learner, it is `(ε, δ)`-private in the adaptive single-challenge model on all inputs (and hence
under replacement on fixed streams), and on every input strategy satisfying (A1) and (A2),
`P[M_T ≤ min{T, 2KU}] ≥ 1 − β`.

**Formalization Note** The accuracy clause quantifies over every input strategy satisfying
(A1)–(A2), realizable or not (a family satisfying them is a set of such strategies). -/
theorem theorem_4_1 {X Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (K m T : ℕ) (agg : (Fin m → U) → X → Bool) (κ : (X → Bool) → X × Bool → Option Z)
    (gfb : X → Bool) (ε δ β : ℝ) (hK : 1 ≤ K) (hm : 1 ≤ m) (hT : 1 ≤ T) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hβ : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hcap : 20 * (Real.log ((sys.C []).card : ℝ) + aP K m T B ε δ * (D : ℝ) + 1) < (K : ℝ)) :
    let P : Alg1Spec X Z U D B :=
      { sys := sys, K := K, m := m, T := T, η := etaP K m ε δ, a := aP K m T B ε δ,
        Uth := Uth K m T ε δ β, εa := epsA ε, agg := agg, κ := κ, gfb := gfb }
    (continualLearner P).IsRegular T ∧
      IsAdaptivePrivate (continualLearner P) T ε δ ∧
      IsReplacementPrivate (continualLearner P) T ε δ ∧
      ∀ inp : InputStrategy X T, IsA1 P inp → IsA2 P β inp →
        ENNReal.ofReal (1 - β) ≤ (continualLearner P).μ
          {ω | (gameMistakes (continualLearner P) inp ω : ℝ) ≤
            min (T : ℝ) (2 * (K : ℝ) * Uth K m T ε δ β)} := by sorry

end PrivLittlestone

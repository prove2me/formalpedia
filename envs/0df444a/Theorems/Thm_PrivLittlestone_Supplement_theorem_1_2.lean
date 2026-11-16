-- Prove2me | Theorems.Thm_PrivLittlestone_Supplement_theorem_1_2
-- name    : PrivLittlestone.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:59:16.164786+00:00
-- url     : https://prove2.me/theorems/34aa8bdd-4302-47bc-b16c-61bf2e7efe6d
-- title:
--   Theorem 1.2 — proper adaptive $(\varepsilon,\delta)$-private learner for flats of rank $\le r$ and subspaces of dimension $\le r$ with $O(r^{3/2}\Lambda_r^{5/2}/\varepsilon)$ mistakes
-- statement:
--   Let $C$ be a universal constant. For $T \ge 1$, $0 < \varepsilon \le 1$ and $0 < \delta, \beta \le 1/2$ write
--   $$
--   \Lambda_r = \log \frac{e(r+1)(T+1)}{\varepsilon\delta\beta}.
--   $$
--   Let $M$ be a finite matroid of rank at least $r \ge 1$ and $H_r(M)$ the class of indicators of its flats of rank at most $r$. Then there is an online learner such that:
--
--   1. it is $(\varepsilon,\delta)$-private on all inputs, in the adaptive single-challenge model and under replacement;
--   2. it is **proper** on arbitrary inputs: every classifier it releases is the indicator of a flat of rank at most $r$;
--   3. against every adaptive adversary producing a sequence realizable by $H_r(M)$, even one that observes the current classifier before choosing the next example, its number of mistakes $M_T$ over $T$ rounds satisfies
--   $$
--   \Pr\Big[ M_T \le \min\Big\{ T,\ \frac{C\, r^{3/2} \Lambda_r^{5/2}}{\varepsilon} \Big\} \Big] \ge 1 - \beta .
--   $$
--
--   The same holds, with the same constant $C$, for the class of subspaces of dimension at most $r$ of $\mathbb F^{D_{\mathrm{amb}}}$, for every field $\mathbb F$ and every $D_{\mathrm{amb}}$: the mistake bound does not depend on $D_{\mathrm{amb}}$ or on the field.
--
--   This is the paper's geometric application: the rank exponent $3/2$ improves the exponent $2$ of fresh-buffer restart, and properness holds against current-classifier adaptive inputs.
--
--   **Formalization Note** $C$ is chosen before every other quantifier, and one $C$ serves the matroid and the subspace parts. The learner is regular (probability coins, measurable releases of countable range). The adversary is a deterministic input strategy seeing the classifiers released so far, including the current one; its run is required to be realizable almost surely, by a target that may depend on the run.
--
--   Differences from the source:
--
--   - encoding: instances are the elements of the ground set E of M → instances range over the element type α of the Mathlib matroid, with M.E ⊆ α; reason: no flat contains an element outside E, so every class member and every realizable label is 0 there and the learner's releases (flats) are 0 there too; same mistakes
--   - encoding: every adaptive adversary, which may see the current classifier before choosing the next example → every deterministic InputStrategy, which sees g_0, …, g_t before supplying z_t; reason: the base mission's model; a randomized adversary is a mixture of deterministic ones and the probability bound integrates
--   - reading: an adaptive adversary producing a realizable sequence → the run's records are realizable by the class almost surely, by a target that may depend on the run; reason: §6.2, p.11: the argument 'holds pathwise even when the entire adaptive interaction determines the realizing target'; the weakest hypothesis, as in the base mission's (A1)
--   - reading: (ε, δ)-private online learner → regular, and (ε, δ)-private both in the adaptive single-challenge model (Definition 2.1) and under replacement (§2.1), on all inputs; reason: the paper's two privacy notions, the first implying the second (§2.1); regularity is §2's measurability and finite-support convention; as in the published Theorem 1.1
--   - encoding: every output is a rank-at-most-r flat on arbitrary inputs → for every round t < T, every history and every coin, the release lies in H_r(M) (resp. the subspace class); reason: the outputs of a horizon-T learner are its releases at rounds 0, …, T − 1
--   - generalization: subspaces of dimension at most r in F^{D_amb}, which §6 (p.10) places in an ambient space of dimension at least r, the analogue of the matroid's rank ≥ r → every D_amb, with no condition r ≤ D_amb; reason: on D_amb ≥ r it is the source's statement; for D_amb < r the class equals the class for r = D_amb and the bound for r is larger
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Theorem 1.2, p.2 (proof §6.3, p.12)

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner_IsRegular
import Definitions.Def_PrivLittlestone_IsAdaptivePrivate
import Definitions.Def_PrivLittlestone_IsReplacementPrivate
import Definitions.Def_PrivLittlestone_gameMistakes
import Definitions.Def_PrivLittlestone_IsRealizableBy
import Definitions.Def_PrivLittlestone_bigLam
import Definitions.Def_PrivLittlestone_Supplement_flatClass
import Definitions.Def_PrivLittlestone_Supplement_subspaceClass

universe u v

namespace PrivLittlestone.Supplement

open MeasureTheory

/-- **Theorem 1.2 (Proper adaptive learning of flats)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Theorem 1.2, p.2; proof §6.3, p.12). Let `C` be a universal constant; for `T ≥ 1`, `0 < ε ≤ 1`,
`0 < δ, β ≤ 1/2` write `Λ_r = log(e(r + 1)(T + 1)/(εδβ))`. For every finite matroid `M` of rank at
least `r ≥ 1` there is a proper `(ε, δ)`-private online learner for `H_r(M)` with
`P[M_T ≤ min{T, C r^{3/2} Λ_r^{5/2}/ε}] ≥ 1 − β` against every adaptive adversary producing a
realizable sequence, even if it observes the current classifier before choosing the next example;
every output is a flat of rank at most `r` on arbitrary inputs. The same holds for subspaces of
dimension at most `r` of `𝔽^{D_amb}` over any field, with the same `C`.

**Formalization Note** `C` is chosen before every other quantifier (it may formally depend on the
universe levels) and one `C` serves the matroid and the subspace parts, for every field and every
`D_amb`. "(ε, δ)-private" is asserted in both senses of the paper (adaptive single-challenge,
Definition 2.1, and replacement, §2.1) on all inputs, with regularity. Properness: at every round
`t < T`, for every history (realizable or not) and every coin, the release is in the class. The
adaptive adversary is a deterministic `InputStrategy` that sees the current classifier; its run is
required to be realizable by the class almost surely, by a target that may depend on the run. The
instance type is the matroid's element type `α` (elements outside `M.E` lie in no flat). The
subspace part is stated for every `D_amb`, as the theorem's sentence is; it does not assume
`r ≤ D_amb` (for `D_amb < r` the class is that of `r = D_amb` and the bound for `r` is larger). -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (α : Type u) (M : Matroid α) (r : ℕ), M.Finite → 1 ≤ r → (r : ℕ∞) ≤ M.eRank →
        ∀ (T : ℕ) (ε δ β : ℝ), 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 → 0 < β → β ≤ 1 / 2 →
          ∃ A : OnlineLearner α, A.IsRegular T ∧
            IsAdaptivePrivate A T ε δ ∧ IsReplacementPrivate A T ε δ ∧
            (∀ t : ℕ, t < T → ∀ (hist : Fin t → α × Bool) (ω : A.Ω),
              A.release t hist ω ∈ flatClass M r) ∧
            ∀ inp : InputStrategy α T,
              (∀ᵐ ω ∂A.μ, IsRealizableBy (flatClass M r) (playRecords A inp ω)) →
              ENNReal.ofReal (1 - β) ≤ A.μ {ω |
                (gameMistakes A inp ω : ℝ) ≤
                  min (T : ℝ) (C * (r : ℝ) ^ (3 / 2 : ℝ) * (bigLam r T ε δ β) ^ (5 / 2 : ℝ) / ε)}) ∧
      (∀ (𝕜 : Type v) [Field 𝕜] (D r : ℕ), 1 ≤ r →
        ∀ (T : ℕ) (ε δ β : ℝ), 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 → 0 < β → β ≤ 1 / 2 →
          ∃ A : OnlineLearner (Fin D → 𝕜), A.IsRegular T ∧
            IsAdaptivePrivate A T ε δ ∧ IsReplacementPrivate A T ε δ ∧
            (∀ t : ℕ, t < T → ∀ (hist : Fin t → (Fin D → 𝕜) × Bool) (ω : A.Ω),
              A.release t hist ω ∈ subspaceClass 𝕜 D r) ∧
            ∀ inp : InputStrategy (Fin D → 𝕜) T,
              (∀ᵐ ω ∂A.μ, IsRealizableBy (subspaceClass 𝕜 D r) (playRecords A inp ω)) →
              ENNReal.ofReal (1 - β) ≤ A.μ {ω |
                (gameMistakes A inp ω : ℝ) ≤
                  min (T : ℝ) (C * (r : ℝ) ^ (3 / 2 : ℝ) * (bigLam r T ε δ β) ^ (5 / 2 : ℝ) / ε)}) := by sorry

end PrivLittlestone.Supplement

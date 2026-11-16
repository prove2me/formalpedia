-- Prove2me | Theorems.Thm_PrivLittlestone_Supplement_theorem_7_2
-- name    : PrivLittlestone.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:59:55.129548+00:00
-- url     : https://prove2.me/theorems/a8a44adc-2b1c-4b58-9087-ca878757d751
-- title:
--   Theorem 7.2 — adaptive $(\varepsilon,\delta)$-private learner with $O(d^{3/2}(\sqrt{v+1}L_v^2+L_v^{5/2})/\varepsilon)$ mistakes from dual VC dimension $v$
-- statement:
--   Let $H \subseteq \{0,1\}^X$ have Littlestone dimension $d \ge 1$, let $U$ be the universe of Proposition 5.1 (the locally realizable universe $U = \{h \in \{0,1\}^X : H[h,A] \ne \emptyset \text{ whenever } |A| \le d+1\}$), let $v^* = \mathrm{VCdim}(U^*)$ be the VC dimension of its dual class $U^* = \{R_x : x \in X\}$, $R_x = \{h \in U : h(x) = 1\}$, and let $v \ge v^*$ be an integer. For $T \ge 1$, $0 < \varepsilon \le 1$ and $0 < \delta, \beta \le 1/2$ put
--   $$
--   L_v = \log \frac{e(d+1)(v+1)(T+1)}{\varepsilon\delta\beta}.
--   $$
--   Then, for a universal constant $C$, there is an online learner, possibly improper, that is $(\varepsilon,\delta)$-private on all inputs (in the adaptive single-challenge model, for its full hypothesis transcript, and under replacement) and such that, against every adaptive adversary producing a sequence realizable by $H$, even one that chooses the current example after observing the current classifier,
--   $$
--   \Pr\Big[ M_T \le \min\Big\{ T,\ \frac{C\, d^{3/2}\big(\sqrt{v+1}\, L_v^2 + L_v^{5/2}\big)}{\varepsilon} \Big\} \Big] \ge 1 - \beta .
--   $$
--
--   This is the general adaptive guarantee of the paper: the accuracy of Theorem 1.1 extends to current-classifier adaptive inputs at the price of the dual VC dimension of the candidate universe. With $v = 2^{d+1} - 1$ it gives the singly exponential bound of Corollary 7.3.
--
--   **Formalization Note** $C$ is chosen before every other quantifier. $U$ is the published `localUniverse H d`; $U^*$ is the published binary dual class `BalcanDDA.Piecewise.dualB U`, the evaluation maps $h \mapsto h(x)$ on $U$ (the indicators of the ranges $R_x$); and $v \ge v^*$ is `UnderstandingML.vcDim (dualB U) ≤ v` in $\mathbb N \cup \{\infty\}$. The learner is regular and its releases range over all classifiers. The adversary is a deterministic input strategy seeing the classifiers released so far, including the current one; its run is required to be realizable by $H$ almost surely, by a target that may depend on the run. $\log$ is the natural logarithm.
--
--   Differences from the source:
--
--   - encoding: v ≥ v* = VCdim(U*) for a public integer v → v : ℕ with UnderstandingML.vcDim (BalcanDDA.Piecewise.dualB U) ≤ v in ℕ∞; reason: dualB U is the set of evaluation maps h ↦ h(x) on U, the indicators of the ranges R_x, so its VC dimension is VCdim(U*); same condition, including v* = ∞ (no such v)
--   - encoding: U the universe in Proposition 5.1 → U = localUniverse H d, the locally realizable universe F_0 of Appendix A.2.1; reason: Lemma D.1 (p.25) calls this set 'The universe U of Proposition 5.1'; published definition of the base mission
--   - encoding: every adaptive adversary, which may choose the current example after observing the current classifier → every deterministic InputStrategy, which sees g_0, …, g_t before supplying z_t; reason: the base mission's model; a randomized adversary is a mixture of deterministic ones and the probability bound integrates
--   - reading: an adaptive adversary producing a sequence realizable by H → the run's records are realizable by H almost surely, by a target that may depend on the run; reason: the weakest hypothesis, as in the base mission's (A1); the proof's coverage argument is pathwise
--   - reading: (ε, δ)-private online learner; its full hypothesis transcript satisfies adaptive single-challenge privacy on all inputs → regular, and (ε, δ)-private both in the adaptive single-challenge model and under replacement, on all inputs; reason: the paper's two privacy notions, the first implying the second (§2.1); regularity is §2's measurability convention; as in the published Theorem 1.1
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Theorem 7.2, p.13

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner_IsRegular
import Definitions.Def_PrivLittlestone_IsAdaptivePrivate
import Definitions.Def_PrivLittlestone_IsReplacementPrivate
import Definitions.Def_PrivLittlestone_gameMistakes
import Definitions.Def_PrivLittlestone_IsRealizableBy
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_UnderstandingML_VC

universe u

namespace PrivLittlestone.Supplement

open MeasureTheory

/-- **Theorem 7.2 (Adaptive guarantee from dual VC dimension)** (He–He, *Private Online Learning
of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Theorem 7.2, p.13). Let `LDim(H) = d ≥ 1`, let `U` be the universe of
Proposition 5.1 (the locally realizable universe of Appendix A.2.1), and let `v ≥ v^* =
VCdim(U^*)` be a public integer. For the parameter ranges of Theorem 1.1 put
`L_v = log(e(d + 1)(v + 1)(T + 1)/(εδβ))`. There is an `(ε, δ)`-private online learner such that,
against every adaptive adversary producing a sequence realizable by `H`,
`P[M_T ≤ min{T, C d^{3/2}(√(v + 1) L_v² + L_v^{5/2})/ε}] ≥ 1 − β`. The adversary may choose the
current example after observing the current classifier; the learner can be improper; its full
hypothesis transcript satisfies adaptive single-challenge privacy on all inputs.

**Formalization Note** `C` is chosen before every other quantifier (it may formally depend on the
universe level of `X`). `U` is the published `localUniverse H d`; `U^*` is the published binary
dual class `BalcanDDA.Piecewise.dualB U`, the evaluation maps `h ↦ h(x)` on the subtype `U` (the
indicators of the ranges `R_x`), and `v ≥ v^*` is `UnderstandingML.vcDim (dualB U) ≤ v` in `ℕ∞`.
`LDim` is the published `UnderstandingML.ldim`; `d ≥ 1` forces `H` nonempty. Privacy is
asserted in both senses (adaptive single-challenge and replacement) on all inputs, with
regularity; releases range over all of `X → Bool` (improper). The adaptive adversary is a
deterministic `InputStrategy` seeing the current classifier, whose run is realizable by `H`
almost surely, by a target that may depend on the run. `log` is the natural logarithm. -/
theorem theorem_7_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (H : Set (X → Bool)) (d : ℕ),
        UnderstandingML.ldim H = d → 1 ≤ d →
        ∀ v : ℕ,
          UnderstandingML.vcDim (BalcanDDA.Piecewise.dualB (PrivLittlestone.localUniverse H d)) ≤ v →
        ∀ (T : ℕ) (ε δ β : ℝ), 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 → 0 < β → β ≤ 1 / 2 →
          ∃ A : OnlineLearner X, A.IsRegular T ∧
            IsAdaptivePrivate A T ε δ ∧ IsReplacementPrivate A T ε δ ∧
            ∀ inp : InputStrategy X T,
              (∀ᵐ ω ∂A.μ, IsRealizableBy H (playRecords A inp ω)) →
              ENNReal.ofReal (1 - β) ≤ A.μ {ω |
                (gameMistakes A inp ω : ℝ) ≤
                  min (T : ℝ)
                    (C * (d : ℝ) ^ (3 / 2 : ℝ) *
                      (Real.sqrt ((v : ℝ) + 1) *
                          (Real.log (Real.exp 1 * ((d : ℝ) + 1) * ((v : ℝ) + 1) * ((T : ℝ) + 1) /
                            (ε * δ * β))) ^ (2 : ℕ) +
                        (Real.log (Real.exp 1 * ((d : ℝ) + 1) * ((v : ℝ) + 1) * ((T : ℝ) + 1) /
                            (ε * δ * β))) ^ (5 / 2 : ℝ)) / ε)} := by sorry

end PrivLittlestone.Supplement

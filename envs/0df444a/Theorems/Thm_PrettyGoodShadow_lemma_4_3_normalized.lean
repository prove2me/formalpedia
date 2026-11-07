-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_3_normalized
-- name    : PrettyGoodShadow.lemma_4_3_normalized
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:34.533733+00:00
-- url     : https://prove2.me/theorems/b2f91597-3976-4e4a-8eb8-2bbd60ec1db4
-- title:
--   Lemma 4.3, normalized as in §4.1 — $k\ge12/\varepsilon^2$ for $0\preceq A\preceq I$, $k\ge48/\varepsilon^2$ for $\|A\|_\infty\le1$
-- statement:
--   Let $p$ be a prior, $\varepsilon>0$ and $k,T$ with $T\ge1$. In each of the two cases (i) $0\preceq A\preceq I$ and $k\ge12/\varepsilon^2$, (ii) $A$ Hermitian, $\|A\|_\infty\le1$ and $k\ge48/\varepsilon^2$,
--
--   $$
--   \Pr_{x\sim p}\Big[\Pr_{\hat o\sim\mathcal A(x)}\big[|\hat o-\operatorname{tr}(A\rho_x)|>\varepsilon\big]>\tfrac18\Big]\le2e^{-T/128}.
--   $$
--
--   This is what the source's proof on pp.19–22 establishes, under its normalization on p.19. It is the form used in the proof of the goal.
--
--   **Formalization Note** Case (ii) is case (i) for $(I+A)/2$ at accuracy $\varepsilon/2$. The literal form printed on p.18 is the separate item `lemma_4_3`.
--
--   Differences from the source:
--   - reading: Lemma 4.3 prints k = ⌈12/ε²⌉ with ∥O_i∥∞ ≤ 1 (Problem 4.1); §4.1 assumes 0 ⪯ O_i ⪯ I after passing to accuracy ε/2 → (i) 0 ⪯ A ⪯ I with k ≥ 12/ε²; (ii) ∥A∥∞ ≤ 1 with k ≥ 48/ε²; reason: this is what the proof gives; the literal printed form is kept at full strength as the separate item lemma_4_3, so nothing of the printed claim is dropped from the mission
--   - generalization: k = ⌈12/ε²⌉ → every k above the threshold; reason: the proof uses only 4e^{−kε²/2} ≤ 1/16, and the ceiling is one such k
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.3, p.18; normalization §4.1, p.19; proof pp.21–22

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_alg1Law

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow

/-- **Lemma 4.3, normalized as in §4.1** (arXiv:2610.06781, sha256 bd055b7d…, p.18; normalization p.19; proof pp.21–22).
For a prior `p`, every `ε > 0`, `T ≥ 1` and `k` above the threshold, the conclusion
`Pr_{x∼p}[Pr_{ô∼A(x)}[|ô − tr(A ρ_x)| > ε] > 1/8] ≤ 2 e^{−T/128}` holds in two cases:
(i) `0 ⪯ A ⪯ I` and `k ≥ 12/ε²`; (ii) `A` Hermitian, `‖A‖_∞ ≤ 1` and `k ≥ 48/ε²`.

**Formalization Note** Case (ii) is case (i) for `(I + A)/2` at accuracy `ε/2`: "estimating the expectation of
`(I + O_i)/2` to `±ε/2` accuracy suffices" (p.19). The form printed on p.18 is the separate item `lemma_4_3`. Every
`k` above the threshold is allowed, since the proof uses only `4 e^{−kε²/2} ≤ 1/16`. -/
theorem lemma_4_3_normalized {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (p : L → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (A : Matrix d d ℂ) (ε : ℝ) (hε : 0 < ε) (k T : ℕ)
    (hT : 1 ≤ T) :
    (QAlgorithms.IsEffect A → 12 / ε ^ 2 ≤ (k : ℝ) →
      ∑ x with 1 / 8 < errProb p ρ k T A ε x, p x ≤ 2 * Real.exp (-(T : ℝ) / 128)) ∧
    (A.IsHermitian → ‖A‖ ≤ 1 → 48 / ε ^ 2 ≤ (k : ℝ) →
      ∑ x with 1 / 8 < errProb p ρ k T A ε x, p x ≤ 2 * Real.exp (-(T : ℝ) / 128)) := by sorry

end PrettyGoodShadow

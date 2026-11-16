-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_theorem_22
-- name    : TFIMPhaseDiagram.Classical.Supplement.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:53.294179+00:00
-- url     : https://prove2.me/theorems/e1346bd1-2e15-4acf-9943-cfdd24afbff0
-- title:
--   Theorem 22 — Exponential L² concentration at both magnetizations
-- statement:
--   Fix $b,\eta>0$ with $(b/\eta)\tanh\eta>1$. There exist a magnetization $m_\ast\in(0,1)$ and a constant $c>0$ depending only on $b,\eta$, such that for every $\delta>0$ there is an integer $n_0>0$ for which every $n\ge n_0$ satisfies
--   $$
--   \Pr_{\sigma\sim\mu_n}\!\left[\bar\sigma\notin B(m_\ast1,\delta)\cup B(-m_\ast1,\delta)\right]\le e^{-nc\delta^2}.
--   $$
--   The balls use the full Hilbert norm, $\bar\sigma=n^{-1}\sum_i\sigma_i$, and $\mu_n$ is the continuous spin-path Curie–Weiss law. The statement uses the shared positive magnetization and $c=c_{\mathrm{gap}}/2$ exactly as chosen in the proof on p.18. The radius is unrestricted apart from positivity; the threshold may depend on the radius. This is the concentration companion theorem for the hardness branch.
--
--   Differences from the source:
--   - encoding: existential magnetization and parameter-dependent constant, chosen in the proof on p.18 → the shared positive stationary root and half the explicit Lemma 27 gap; reason: records the source proof witnesses before the radius and system size are quantified
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 15, Theorem 22

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Theorem 22, p.15. The source proof on p.18 chooses half the functional gap. -/
theorem theorem_22 (b η : ℝ) (h : supercritical b η) :
    IsMagnetization b η (magnetization b η) ∧ 0 < functionalGap b η / 2 ∧
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (cwLaw b η n).real {σ | δ ≤ ‖averageL2 σ - constL2 (magnetization b η)‖ ∧
        δ ≤ ‖averageL2 σ - constL2 (-magnetization b η)‖} ≤
        Real.exp (-(n : ℝ) * (functionalGap b η / 2) * δ^2) := by sorry

end TFIMPhaseDiagram.Classical.Supplement

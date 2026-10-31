-- Prove2me | Theorems.Thm_ReviewProvision_lemma_8
-- name    : ReviewProvision.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:06.035981+00:00
-- url     : https://prove2.me/theorems/c9240ded-4aa2-402a-8345-09b5290945aa
-- title:
--   Lemma 8, p.36 — monotonicity of $g$ and $\tilde g$
-- statement:
--   For $\sigma>0$ let
--
--   $$
--   g(\sigma)=\int_{-1/\sigma}^{+\infty}z\Bigl(z+\frac1\sigma\Bigr)\phi(z)\,dz,\qquad
--   \tilde g(\sigma)=\int_{-1/\sigma}^{+\infty}z(z\sigma+1)\phi(z)\,dz .
--   $$
--
--   Then $g$ is strictly decreasing and $\tilde g$ strictly increasing on $(0,\infty)$, $\lim_{\sigma\to0^+}g(\sigma)=1$, and $g(\sigma)>0$ for every $\sigma>0$.
--
--   These functions are the sensitivity of the second-period payoff to the variance, so this is what controls the first-order conditions.
--
--   Differences from the source:
--   - generalization: Lemma 8: monotonicity and the limit → also g(σ) > 0 for all σ > 0; reason: p.45 cites this 'By Lemma 8' though the Lemma does not state it; the rest of the statement is the printed one
--   - reading: 'decreases', 'increases' → strictly; reason: the proof on p.36 shows derivatives < 0 and > 0
--   - encoding: σ unrestricted → σ ∈ (0, ∞); reason: g and g̃ are defined through 1/σ only for σ > 0
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Lemma 8, p.36

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Lemma 8**, SSRN 3403322 (manuscript of 2021-05-24), p.36 (PDF 36): `g` decreases and `g̃`
increases in `σ`, and `lim_{σ→0} g(σ) = 1`. With the positivity `g(σ) > 0` for all `σ > 0`, which p.45
cites "By Lemma 8".

**Formalization Note.** The domain is `σ > 0`, the only one where `g` and `g̃` are defined. Monotonicity
is strict: the proof on p.36 has derivatives `< 0` and `> 0`. -/
theorem lemma_8 :
    StrictAntiOn g (Set.Ioi 0) ∧
    StrictMonoOn gTilde (Set.Ioi 0) ∧
    Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    ∀ σ : ℝ, 0 < σ → 0 < g σ := by sorry

end ReviewProvision

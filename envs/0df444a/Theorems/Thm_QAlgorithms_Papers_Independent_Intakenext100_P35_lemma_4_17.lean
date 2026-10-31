-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_lemma_4_17
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.lemma_4_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:27:32.111585+00:00
-- url     : https://prove2.me/theorems/083903fa-2bb9-4533-b4cc-376b8bf8f7cb
-- title:
--   Lemma 4.17
-- statement:
--   Let $\mathcal A$ be either $\mathcal D_s$, $s>-1$, or $\mathcal H_\psi$, $0<\psi<\pi$. Suppose $(f_k)$ is bounded in $\mathcal A$ and converges pointwise on its native domain to $f$. Let $g\in\mathcal A$ satisfy $g(0)=g(\infty)=0$. For $0<\gamma<1$, write $u_\gamma(z)=u(z^\gamma)$. Then the products belong to $\mathcal A$ and
--
--   $$\|(f_{k,\gamma}-f_\gamma)g_\gamma\|_{\mathcal A}\longrightarrow0.$$
--
--   This supplies the approximation needed for the D- and H-calculus convergence results.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 24, Lemma 4.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Lemma 4.17, arXiv:2202.03143v1, PDF page(s) 24. Source correction: the H case uses its native sector for pointwise convergence and pullbacks, rather than the printed C_+. For wider sectors bounded holomorphic convergence on the intersection determines the same limit. No general algebra structure is assumed for D_s. Independent moderation is pending. -/
theorem lemma_4_17
:
    (∀ s : ℝ, -1 < s → ∀ fs : ℕ → AnalyticSymbol, ∀ f g : AnalyticSymbol,
      (∀ n, D s (fs n)) → (∃ C : ℝ, ∀ n, dSize s (fs n) ≤ ENNReal.ofReal C) →
      (∀ z ∈ hp, Tendsto (fun n => fs n z) atTop (𝓝 (f z))) →
      D s g → zeroValue g = 0 → infinityValue g = 0 →
      ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      (∀ n, D s ((powerPull gamma (fs n) - powerPull gamma f) * powerPull gamma g)) ∧
      NormConverges (dSize s)
        (fun n => (powerPull gamma (fs n) - powerPull gamma f) * powerPull gamma g) 0) ∧
    (∀ psi : ℝ, 0 < psi → psi < Real.pi → ∀ fs : ℕ → AnalyticSymbol, ∀ f g : AnalyticSymbol,
      (∀ n, HardySobolevClass psi (fs n)) → (∃ C : ℝ, ∀ n, hSize psi (fs n) ≤ ENNReal.ofReal C) →
      (∀ z ∈ openSectorDomain psi, Tendsto (fun n => fs n z) atTop (𝓝 (f z))) →
      HardySobolevClass psi g → zeroValue g = 0 → infinityValue g = 0 →
      ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      (∀ n, HardySobolevClass psi ((powerPull gamma (fs n) - powerPull gamma f) * powerPull gamma g)) ∧
      NormConverges (hSize psi)
        (fun n => (powerPull gamma (fs n) - powerPull gamma f) * powerPull gamma g) 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end

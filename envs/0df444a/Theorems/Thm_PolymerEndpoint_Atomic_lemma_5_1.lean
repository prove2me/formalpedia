-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_5_1
-- name    : PolymerEndpoint.Atomic.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:57.125555+00:00
-- url     : https://prove2.me/theorems/8f8a1263-73ad-4a30-a961-60266838bfcb
-- title:
--   Lemma 5.1 — $R$ has unique minimum $R(\mathbf 1)=\mathbb E\log Z_1$ and unique maximum $R(\mathbf 0)=\lambda(\beta)$
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$ and let $R:\mathcal S\to\mathbb R$ be the functional of (3.8),
--
--   $$
--   R(f)=\mathbb E\log\frac{\widetilde F}{2d},\qquad \widetilde F=\sum_{u}\sum_{v\sim u}f(v)e^{\beta Y_u}+2d(1-\|f\|)e^{\lambda(\beta)},
--   $$
--
--   where $(Y_u)$ are i.i.d. with law $\mathfrak L$. Then $R$ achieves a unique minimum $R(\mathbf 1)=\mathbb E\log Z_1$ and a unique maximum $R(\mathbf 0)=\lambda(\beta)$:
--
--   1. $R(\mathbf 1)\leq R(f)\leq R(\mathbf 0)$ for every $f\in\mathcal S$;
--   2. $R(f)=R(\mathbf 1)$ if and only if $f=\mathbf 1$ in $\mathcal S$, i.e. $f(u)=1$ for some cell $u$;
--   3. $R(f)=R(\mathbf 0)$ if and only if $f=\mathbf 0$, i.e. $\|f\|=0$;
--   4. $R(\mathbf 1)=\mathbb E\log Z_1$ and $R(\mathbf 0)=\lambda(\beta)$.
--
--   The two extreme values are the free energies of the two phases' extreme fixed points, $\delta_{\mathbf 1}$ and $\delta_{\mathbf 0}$.
--
--   **Formalization Note** The paper's standing assumption $\beta>0$ (§1.1) is kept: at $\beta=0$, $\widetilde F\equiv2d$, $R\equiv0$ and neither extremum is unique. $\mathbf 1$ is represented by the unit mass at cell $(0,0)$ and $\mathbf 0$ by the zero function; uniqueness is stated up to the identification of $\mathcal S$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 38, Lemma 5.1 (with (3.8), p. 27)

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem lemma_5_1 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β) :
    (∀ f : PSM d, R 𝔏 β (one (d := d)) ≤ R 𝔏 β f ∧ R 𝔏 β f ≤ R 𝔏 β (0 : PSM d)) ∧
    (∀ f : PSM d, R 𝔏 β f = R 𝔏 β (one (d := d)) ↔ ∃ u : Cell d, f.toFun u = 1) ∧
    (∀ f : PSM d, R 𝔏 β f = R 𝔏 β (0 : PSM d) ↔ mass f = 0) ∧
    R 𝔏 β (one (d := d)) =
      ∫ Y, Real.log (Z (fun u (Y : Cell d → ℝ) => Y u) β 1 Y) ∂(envLaw (d := d) 𝔏) ∧
    R 𝔏 β (0 : PSM d) = logMGF 𝔏 β := by sorry

end PolymerEndpoint.Atomic

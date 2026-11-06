-- Prove2me | Theorems.Thm_TiltedCvx_example_3
-- name    : TiltedCvx.example_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:57.005456+00:00
-- url     : https://prove2.me/theorems/03c36f78-1fe7-4e2c-b248-48967c03da0b
-- title:
--   Example 3 — $\vartheta_\gamma$ has $\gamma^*_{\mathrm{sec}}=\eta(\gamma)$ (corrected: $\gamma<1$ for two clauses)
-- statement:
--   Fix $\gamma\in(0,1]$ and let $\vartheta_\gamma(s)=\min\{s^\gamma,1-(1-s)^{1/\gamma}\}$ for $s\in[0,1]$ and $\vartheta_\gamma(s)=+\infty$ otherwise; let $\tau_\gamma$ and $\eta(\gamma)=(\tau_\gamma/(1-\tau_\gamma))^2$ be as in Theorem 22. Then $\vartheta_\gamma$ is proper and lower semicontinuous, and
--
--   $$
--   \gamma^*_{\mathrm{mono}}(\vartheta_\gamma)=\gamma^2,\qquad\gamma^*_{\mathrm{sec}}(\vartheta_\gamma)=\eta(\gamma),\qquad\gamma^*(\vartheta_\gamma)=\gamma .
--   $$
--
--   If moreover $\gamma<1$, then $\eta(\gamma)\in(\gamma^2,\gamma)$ and $\vartheta_\gamma\notin\mathcal F^\gamma_{\mathrm{sec}}$. In all cases $\vartheta_\gamma\in\mathcal F^\gamma\subseteq\mathcal F^{\gamma^2}_{\mathrm{mono}}\subseteq\mathcal F^{\gamma^2}_{\mathrm{sec}}$.
--
--   This profile shows that the third inclusion of the main chain is strict and that implication (i) of Corollary 8 is sharp.
--
--   **Formalization Note** The chain is $\vartheta_\gamma\in\mathcal F^\gamma$ together with the two class inclusions on $\mathbb R$.
--
--   Differences from the source:
--   - correction: for γ ∈ (0, 1]: η(γ) ∈ (γ², γ) and ϑγ ∉ F^γ_sec → these two clauses for γ ∈ (0, 1) only; all other clauses for γ ∈ (0, 1]; reason: false at γ = 1: η(1) = 1 (Theorem 22) so (1, 1) is empty, and ϑ₁(s) = s on [0, 1] (+∞ elsewhere) is proper, lsc and convex, hence in F¹_sec (Theorem 19(ii)); the appendix proof (p.112) treats γ = 1 separately
--   - encoding: the printed 'f' in 'f ∉ F^γ_sec, f ∈ F^γ …' → ϑγ; reason: the only function of the example
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Example 3, p.29

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_classMono
import Definitions.Def_TiltedCvx_classSec
import Definitions.Def_TiltedCvx_gammaStar
import Definitions.Def_TiltedCvx_gammaMono
import Definitions.Def_TiltedCvx_gammaSec
import Definitions.Def_TiltedCvx_eta
import Definitions.Def_TiltedCvx_theta

namespace TiltedCvx

/-- **Example 3 (corrected: `γ < 1` in two clauses).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Example 3, p.29. Fix `γ ∈ (0, 1]` and let `ϑγ(s) = min{s^γ, 1 − (1 − s)^{1/γ}}`
on `[0, 1]`, `+∞` off `[0, 1]`; let `τγ`, `η(γ)` be as in Theorem 22. Then `ϑγ` is proper and lsc,
`γ*_mono(ϑγ) = γ²`, `γ*_sec(ϑγ) = η(γ) ∈ (γ², γ)`, `γ*(ϑγ) = γ`. In particular `ϑγ ∉ F^γ_sec`
and `ϑγ ∈ F^γ ⊆ F^{γ²}_mono ⊆ F^{γ²}_sec`.

**Formalization Note** Correction: as printed, `η(γ) ∈ (γ², γ)` and `ϑγ ∉ F^γ_sec` are false at
`γ = 1` (`η(1) = 1` by Theorem 22, and `ϑ₁(s) = s` on `[0, 1]` is convex, hence in `F¹_sec`); these
two clauses carry `γ < 1`, all others hold on `(0, 1]`. The printed "`f`" of the last display is
`ϑγ`. On `ℝ`; the chain is `ϑγ ∈ F^γ` plus the two class inclusions on `ℝ`. -/
theorem example_3 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    IsProper (theta γ) ∧ LowerSemicontinuous (theta γ) ∧
    gammaMono (theta γ) = γ ^ 2 ∧ gammaSec (theta γ) = eta γ ∧ gammaStar (theta γ) = γ ∧
    (γ < 1 → (γ ^ 2 < eta γ ∧ eta γ < γ) ∧
      theta γ ∉ (classSec γ : Set (ℝ → EReal))) ∧
    theta γ ∈ (classF γ : Set (ℝ → EReal)) ∧
    (classF γ : Set (ℝ → EReal)) ⊆ classMono (γ ^ 2) ∧
    (classMono (γ ^ 2) : Set (ℝ → EReal)) ⊆ classSec (γ ^ 2) := by sorry

end TiltedCvx

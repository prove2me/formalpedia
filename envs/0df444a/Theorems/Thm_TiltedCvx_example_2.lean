-- Prove2me | Theorems.Thm_TiltedCvx_example_2
-- name    : TiltedCvx.example_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:03.075045+00:00
-- url     : https://prove2.me/theorems/ec032abe-7133-4d7d-9c35-220163aa7ae5
-- title:
--   Example 2 — $x/(1+cx)$ has $\gamma^*_{\mathrm{sec}}=\gamma^*=(\gamma^*_{\mathrm{mono}})^{1/2}=\gamma$
-- statement:
--   Fix $\gamma\in(0,1)$, put $c:=(1-\gamma)/\gamma$, and let $f(x)=x/(1+cx)$ for $x\in[0,1]$ and $f(x)=+\infty$ elsewhere. Then $f$ is proper and lower semicontinuous, its restriction to $[0,1]$ is continuously differentiable, and
--
--   $$
--   \gamma^*_{\mathrm{sec}}(f)=\gamma^*(f)=\big(\gamma^*_{\mathrm{mono}}(f)\big)^{1/2}=\gamma .
--   $$
--
--   Therefore $f\notin\mathcal F^\gamma_{\mathrm{mono}}$ and $f\in\mathcal F^\gamma_{\mathrm{sec}}\subseteq\mathcal F^\gamma\subseteq\mathcal F^{\gamma^2}_{\mathrm{mono}}$.
--
--   This function shows that the second inclusion of the main chain is strict and that implication (iii) of Corollary 8 is sharp.
--
--   **Formalization Note** Continuous differentiability of the restriction is `ContDiffOn ℝ 1` of the formula on $[0,1]$. The chain is $f\in\mathcal F^\gamma_{\mathrm{sec}}$ together with the two class inclusions on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Example 2, p.29

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_classMono
import Definitions.Def_TiltedCvx_classSec
import Definitions.Def_TiltedCvx_gammaStar
import Definitions.Def_TiltedCvx_gammaMono
import Definitions.Def_TiltedCvx_gammaSec
import Definitions.Def_TiltedCvx_exTwo

namespace TiltedCvx

/-- **Example 2.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Example 2, p.29. Fix
`γ ∈ (0, 1)`, `c := (1 − γ)/γ`, and let `f(x) := x/(1 + cx)` on `[0, 1]`, `+∞` elsewhere. Then
`f` is proper and lsc, its restriction to `[0, 1]` is continuously differentiable, and
`γ*_sec(f) = γ*(f) = (γ*_mono(f))^{1/2} = γ`. Therefore `f ∉ F^γ_mono` and
`f ∈ F^γ_sec ⊆ F^γ ⊆ F^{γ²}_mono`.

**Formalization Note** On `ℝ`. Continuous differentiability of the restriction is `ContDiffOn ℝ 1`
of the formula on `[0, 1]`. The chain is `f ∈ F^γ_sec` plus the two class inclusions on `ℝ`. -/
theorem example_2 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsProper (exTwo γ) ∧ LowerSemicontinuous (exTwo γ) ∧
    ContDiffOn ℝ 1 (fun x : ℝ => x / (1 + ((1 - γ) / γ) * x)) (Set.Icc 0 1) ∧
    gammaSec (exTwo γ) = γ ∧ gammaStar (exTwo γ) = γ ∧ Real.sqrt (gammaMono (exTwo γ)) = γ ∧
    exTwo γ ∉ (classMono γ : Set (ℝ → EReal)) ∧
    exTwo γ ∈ (classSec γ : Set (ℝ → EReal)) ∧
    (classSec γ : Set (ℝ → EReal)) ⊆ classF γ ∧
    (classF γ : Set (ℝ → EReal)) ⊆ classMono (γ ^ 2) := by sorry

end TiltedCvx

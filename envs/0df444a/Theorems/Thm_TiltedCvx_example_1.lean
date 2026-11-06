-- Prove2me | Theorems.Thm_TiltedCvx_example_1
-- name    : TiltedCvx.example_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:46.1594+00:00
-- url     : https://prove2.me/theorems/5635a85d-ccd3-432a-8a91-37290c8b4877
-- title:
--   Example 1 — a function with $\gamma^*_{\mathrm{mono}}=\gamma^*_{\mathrm{sec}}=\gamma^*=\gamma$
-- statement:
--   Fix $\gamma\in(0,1)$ and let $f:\mathbb R\to\overline{\mathbb R}$ be $f(x)=x$ on $[-1,0]$, $f(x)=\gamma x$ on $[0,1]$, and $f(x)=+\infty$ off $[-1,1]$. Then $f$ is proper and lower semicontinuous, and
--
--   $$
--   \gamma^*_{\mathrm{mono}}(f)=\gamma^*_{\mathrm{sec}}(f)=\gamma^*(f)=\gamma .
--   $$
--
--   Therefore $f\notin\mathcal F^{\sqrt\gamma}$ and $f\in\mathcal F^\gamma_{\mathrm{mono}}\subseteq\mathcal F^\gamma_{\mathrm{sec}}\subseteq\mathcal F^\gamma$.
--
--   This function shows that the first inclusion of the main chain is strict and that implication (ii) of Corollary 8 is sharp.
--
--   **Formalization Note** The chain is stated as $f\in\mathcal F^\gamma_{\mathrm{mono}}$ together with the two class inclusions on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Example 1, p.29

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_classMono
import Definitions.Def_TiltedCvx_classSec
import Definitions.Def_TiltedCvx_gammaStar
import Definitions.Def_TiltedCvx_gammaMono
import Definitions.Def_TiltedCvx_gammaSec
import Definitions.Def_TiltedCvx_exOne

namespace TiltedCvx

/-- **Example 1.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Example 1, p.29. Fix
`γ ∈ (0, 1)` and let `f(x) := x` on `[−1, 0]`, `γx` on `[0, 1]`, `+∞` off `[−1, 1]`. Then `f`
is proper and lsc, `γ*_mono(f) = γ*_sec(f) = γ*(f) = γ`, and therefore `f ∉ F^√γ` and
`f ∈ F^γ_mono ⊆ F^γ_sec ⊆ F^γ`.

**Formalization Note** On `ℝ`; the chain `F^γ_mono ⊆ F^γ_sec ⊆ F^γ` is stated as the two class
inclusions on `ℝ`, together with `f ∈ F^γ_mono`. -/
theorem example_1 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsProper (exOne γ) ∧ LowerSemicontinuous (exOne γ) ∧
    gammaMono (exOne γ) = γ ∧ gammaSec (exOne γ) = γ ∧ gammaStar (exOne γ) = γ ∧
    exOne γ ∉ (classF (Real.sqrt γ) : Set (ℝ → EReal)) ∧
    exOne γ ∈ (classMono γ : Set (ℝ → EReal)) ∧
    (classMono γ : Set (ℝ → EReal)) ⊆ classSec γ ∧
    (classSec γ : Set (ℝ → EReal)) ⊆ classF γ := by sorry

end TiltedCvx

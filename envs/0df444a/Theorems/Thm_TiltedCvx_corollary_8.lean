-- Prove2me | Theorems.Thm_TiltedCvx_corollary_8
-- name    : TiltedCvx.corollary_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:13.191833+00:00
-- url     : https://prove2.me/theorems/177830e1-884d-40b2-bd4c-96fdc3446d0f
-- title:
--   Corollary 8 — $\mathcal F^{\sqrt\gamma}\subseteq\mathcal F^\gamma_{mono}\subseteq\mathcal F^\gamma_{sec}\subseteq\mathcal F^\gamma\subseteq\mathcal F^{\eta(\gamma)}_{sec}$, strict and sharp
-- statement:
--   For $\gamma\in(0,1]$ let $\eta(\gamma)$ be the parameter of Theorem 22. Then
--
--   $$
--   \mathcal F^{\sqrt\gamma}\subseteq\mathcal F^\gamma_{\mathrm{mono}}\subseteq\mathcal F^\gamma_{\mathrm{sec}}\subseteq\mathcal F^\gamma\subseteq\mathcal F^{\eta(\gamma)}_{\mathrm{sec}} ,
--   $$
--
--   and if $\gamma\in(0,1)$ every inclusion is strict. Extend $\eta$ by $\eta(0):=0$. Every proper lsc $f:\mathbb R^d\to\overline{\mathbb R}$ satisfies
--
--   $$
--   \big(\gamma^*(f)\big)^2\le\gamma^*_{\mathrm{mono}}(f)\le\gamma^*_{\mathrm{sec}}(f)\le\gamma^*(f),\qquad\eta\big(\gamma^*(f)\big)\le\gamma^*_{\mathrm{sec}}(f).
--   $$
--
--   Moreover, for every $\gamma\in(0,1)$ the following implications are sharp:
--
--   1. if $\gamma^*(f)\ge\gamma$, then $\gamma^*_{\mathrm{mono}}(f)\ge\gamma^2$ and $\gamma^*_{\mathrm{sec}}(f)\ge\eta(\gamma)$; both bounds are attained simultaneously by $\vartheta_\gamma$ of Example 3;
--   2. if $\gamma^*_{\mathrm{mono}}(f)\ge\gamma$, then $\gamma^*_{\mathrm{sec}}(f)\ge\gamma$ and $\gamma^*(f)\ge\gamma$; both bounds are attained simultaneously by the function of Example 1 with parameter $\gamma$;
--   3. if $\gamma^*_{\mathrm{sec}}(f)\ge\gamma$, then $\gamma^*_{\mathrm{mono}}(f)\ge\gamma^2$ and $\gamma^*(f)\ge\gamma$; both bounds are attained simultaneously by the function of Example 2 with parameter $\gamma$.
--
--   This is the exact comparison of the three ways of tilting convexity: through supports, through monotone subdifferentials and through secant slopes.
--
--   **Formalization Note** Strictness is asserted for every nontrivial finite-dimensional space ($d\ge1$); for $d=0$ all classes coincide. "Attained simultaneously" is stated as: the named function on $\mathbb R$ is proper and lsc, satisfies the hypothesis with equality, and both bounds hold with equality.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - reading: if γ ∈ (0, 1), every inclusion in (27) is strict → strict for every nontrivial finite-dimensional E (d ≥ 1); reason: for d = 0 every proper function is convex and the classes coincide, so the claim needs d ≥ 1; it is asserted for every such d, never only d = 1
--   - encoding: attained simultaneously by ϑγ, Example 1, Example 2 → each named function is proper and lsc and its three parameters equal γ (or γ², η(γ)) as listed; reason: the hypothesis holds with equality and both bounds are equalities
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Corollary 8, p.32

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
import Definitions.Def_TiltedCvx_exOne
import Definitions.Def_TiltedCvx_exTwo

namespace TiltedCvx

/-- **Corollary 8 (the tilted classes nest, strictly and sharply).**
Pedramfar–Khanna–Quinn–Aggarwal, *Tilted Convexity and an Exact Offline–Online Separation*,
arXiv:2611.03472, Corollary 8, p.32. For `γ ∈ (0, 1]`,
`F^√γ ⊆ F^γ_mono ⊆ F^γ_sec ⊆ F^γ ⊆ F^{η(γ)}_sec` (27). If `γ ∈ (0, 1)`, every inclusion in (27)
is strict. With `η(0) := 0`, every proper lsc `f : ℝ^d → ℝ̄` satisfies
`(γ*(f))² ≤ γ*_mono(f) ≤ γ*_sec(f) ≤ γ*(f)` and `η(γ*(f)) ≤ γ*_sec(f)` (28). For every
`γ ∈ (0, 1)` the implications
(i) `γ*(f) ≥ γ ⇒ γ*_mono(f) ≥ γ², γ*_sec(f) ≥ η(γ)`,
(ii) `γ*_mono(f) ≥ γ ⇒ γ*_sec(f) ≥ γ, γ*(f) ≥ γ`,
(iii) `γ*_sec(f) ≥ γ ⇒ γ*_mono(f) ≥ γ², γ*(f) ≥ γ`
are sharp: both bounds are attained simultaneously by `ϑγ` (Example 3), by the Example 1
function, and by the Example 2 function, respectively.

**Formalization Note** `ℝ^d` is a finite-dimensional real inner product space `E`. Strictness is
asserted for nontrivial `E` (`d ≥ 1`): for `d = 0` all classes coincide. "Attained
simultaneously" means the named function, which is proper and lsc on `ℝ`, satisfies the
hypothesis with equality and both bounds with equality (last conjunct). -/
theorem corollary_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    (∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      (classF (Real.sqrt γ) : Set (E → EReal)) ⊆ classMono γ ∧
      (classMono γ : Set (E → EReal)) ⊆ classSec γ ∧
      (classSec γ : Set (E → EReal)) ⊆ classF γ ∧
      (classF γ : Set (E → EReal)) ⊆ classSec (eta γ)) ∧
    (Nontrivial E → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (classF (Real.sqrt γ) : Set (E → EReal)) ⊂ classMono γ ∧
      (classMono γ : Set (E → EReal)) ⊂ classSec γ ∧
      (classSec γ : Set (E → EReal)) ⊂ classF γ ∧
      (classF γ : Set (E → EReal)) ⊂ classSec (eta γ)) ∧
    (∀ f : E → EReal, IsProper f → LowerSemicontinuous f →
      gammaStar f ^ 2 ≤ gammaMono f ∧ gammaMono f ≤ gammaSec f ∧
      gammaSec f ≤ gammaStar f ∧ eta (gammaStar f) ≤ gammaSec f) ∧
    (∀ γ : ℝ, 0 < γ → γ < 1 → ∀ f : E → EReal, IsProper f → LowerSemicontinuous f →
      (γ ≤ gammaStar f → γ ^ 2 ≤ gammaMono f ∧ eta γ ≤ gammaSec f) ∧
      (γ ≤ gammaMono f → γ ≤ gammaSec f ∧ γ ≤ gammaStar f) ∧
      (γ ≤ gammaSec f → γ ^ 2 ≤ gammaMono f ∧ γ ≤ gammaStar f)) ∧
    (∀ γ : ℝ, 0 < γ → γ < 1 →
      (IsProper (theta γ) ∧ LowerSemicontinuous (theta γ) ∧
        gammaStar (theta γ) = γ ∧ gammaMono (theta γ) = γ ^ 2 ∧
        gammaSec (theta γ) = eta γ) ∧
      (IsProper (exOne γ) ∧ LowerSemicontinuous (exOne γ) ∧
        gammaMono (exOne γ) = γ ∧ gammaSec (exOne γ) = γ ∧ gammaStar (exOne γ) = γ) ∧
      (IsProper (exTwo γ) ∧ LowerSemicontinuous (exTwo γ) ∧
        gammaSec (exTwo γ) = γ ∧ gammaMono (exTwo γ) = γ ^ 2 ∧
        gammaStar (exTwo γ) = γ)) := by sorry

end TiltedCvx

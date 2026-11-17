-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_25
-- name    : TiltedCvx.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:35:59.109392+00:00
-- url     : https://prove2.me/theorems/2486a202-fb4f-4803-9cb3-812aa2e2bbf6
-- title:
--   Theorem 25 — strict hierarchy of the tilted classes
-- statement:
--   Let $0<\gamma'<\gamma<1$, and let $\mathcal C^\theta$ stand for $\mathcal F^\theta_{\mathrm{mono}}$ for every $\theta$, for $\mathcal F^\theta_{\mathrm{sec}}$ for every $\theta$, or for $\mathcal F^\theta$ for every $\theta$. Then $\mathcal C^1$ is the class of proper lower semicontinuous convex functions, and
--
--   $$
--   \mathcal C^1\subsetneq\mathcal C^\gamma\subsetneq\mathcal C^{\gamma'}\subsetneq\bigcup_{0<\theta\le1}\mathcal C^\theta=\bigcup_{0<\theta\le1}\mathcal F^\theta\subsetneq\mathcal F^{0^+}\subsetneq\mathcal F^0 .\qquad\text{(29)}
--   $$
--
--   Each family is strictly ordered in its parameter, and all positive-parameter classes lie strictly between the convex functions and the pseudoconvex class $\mathcal F^{0^+}$.
--
--   **Formalization Note** The inclusions and both equalities are stated for every finite-dimensional $E$; strictness is stated for nontrivial $E$ ($d\ge1$).
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f : ℝ^d → ℝ̄ is convex → the published epigraph convexity WassersteinDRO.ConvexLossP1.IsConvexExt f (the epigraph {(x, t) : f x ≤ t} is convex); reason: the standard notion for extended-valued functions; Mathlib's ConvexOn needs an ordered-module codomain, which EReal is not
--   - reading: the strict inclusions ⊊ in ℝ^d → ⊂ under Nontrivial E (d ≥ 1); the inclusions and equalities for every E; reason: for d = 0 every proper function is convex and all the classes coincide, so ℝ^d with d ≥ 1 is the paper's setting; the published corollary_8 uses the same reading
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 25, p.34

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_classMono
import Definitions.Def_TiltedCvx_classSec
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_TiltedCvx_Supplement_classZeroPlus

namespace TiltedCvx.Supplement

/-- **Theorem 25 (strict hierarchy).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Theorem 25, p.34. Let `0 < γ′ < γ < 1`, and let `C^θ` stand for `F^θ_mono` for every `θ`, for
`F^θ_sec` for every `θ`, or for `F^θ` for every `θ`. Then `C¹` is the class of proper lsc convex
functions, and
`C¹ ⊊ C^γ ⊊ C^γ′ ⊊ ⋃_{0<θ≤1} C^θ = ⋃_{0<θ≤1} F^θ ⊊ F^{0+} ⊊ F⁰` (29).

**Formalization Note** The three families are the published `classMono`, `classSec`, `classF`;
`F^{0+}` is `classZeroPlus` and `F⁰` the published `classF 0`. Convexity is the published
epigraph convexity `IsConvexExt`. The inclusions and the two equalities are stated for every
finite-dimensional `E`; strictness (`⊂`) is stated for nontrivial `E`, i.e. `d ≥ 1`: for `d = 0`
there is a single proper function, so all the classes coincide. -/
theorem theorem_25 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ γ' : ℝ) (hγ'0 : 0 < γ') (hγ'γ : γ' < γ) (hγ1 : γ < 1)
    (C : ℝ → Set (E → EReal))
    (hC : C = TiltedCvx.classMono ∨ C = TiltedCvx.classSec ∨ C = TiltedCvx.classF) :
    (C 1 = {f | TiltedCvx.IsProper f ∧ LowerSemicontinuous f ∧
        WassersteinDRO.ConvexLossP1.IsConvexExt f}) ∧
    (C 1 ⊆ C γ ∧ C γ ⊆ C γ' ∧ C γ' ⊆ ⋃ θ ∈ Set.Ioc (0 : ℝ) 1, C θ ∧
      (⋃ θ ∈ Set.Ioc (0 : ℝ) 1, C θ) = ⋃ θ ∈ Set.Ioc (0 : ℝ) 1, TiltedCvx.classF θ ∧
      (⋃ θ ∈ Set.Ioc (0 : ℝ) 1, (TiltedCvx.classF θ : Set (E → EReal))) ⊆ classZeroPlus ∧
      classZeroPlus ⊆ (TiltedCvx.classF 0 : Set (E → EReal))) ∧
    (Nontrivial E →
      C 1 ⊂ C γ ∧ C γ ⊂ C γ' ∧ C γ' ⊂ ⋃ θ ∈ Set.Ioc (0 : ℝ) 1, C θ ∧
      (⋃ θ ∈ Set.Ioc (0 : ℝ) 1, (TiltedCvx.classF θ : Set (E → EReal))) ⊂ classZeroPlus ∧
      classZeroPlus ⊂ (TiltedCvx.classF 0 : Set (E → EReal))) := by sorry

end TiltedCvx.Supplement

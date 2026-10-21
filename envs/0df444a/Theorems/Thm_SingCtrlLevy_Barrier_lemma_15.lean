-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_15
-- name    : SingCtrlLevy.Barrier.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:25.777677+00:00
-- url     : https://prove2.me/theorems/8e43efda-a16f-4716-bbc0-446ba0fe6b9a
-- title:
--   Lemma 15, p. 20 — v(x) ≥ lim sup_{ε↓0} v^(ε)(x)
-- statement:
--   Let $X$ have unbounded variation paths, and let Assumptions 1 and 2 and $q>0$ hold. For $\varepsilon>0$ let $v^{(\varepsilon)}(x)=\inf_{\pi\in\mathcal A^{(\varepsilon)}}v^{(\varepsilon)}_\pi(x)$ be the value function (4.42) of the problem with running cost $f^{(\varepsilon)}$ (anchored at $b^*$ of the original $f$) in place of $f$, the admissible set $\mathcal A^{(\varepsilon)}$ defined with $f^{(\varepsilon)}$ in (2.4). Then, for every $x\in\mathbb R$,
--   $$v(x)\ge\limsup_{\varepsilon\downarrow0}v^{(\varepsilon)}(x).$$
--
--   **Formalization Note** Both value functions are infima in the extended reals $\overline{\mathbb R}$ over strategies admissible from $x$, and the $\limsup$ is taken in $\overline{\mathbb R}$ along $\varepsilon\downarrow0$. The hypothesis of unbounded variation is the scope of §4.2. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 20, Lemma 15 (v^(ε) defined p. 19, (4.42))

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (hUBV : ¬ T.BoundedVariation) (x : ℝ) :
    limsup (fun ε => value P X (fEps f (bstar P X f q C) ε) q C x) (𝓝[>] 0)
      ≤ value P X f q C x := by sorry

end SingCtrlLevy.Barrier

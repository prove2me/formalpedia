-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_8
-- name    : SingCtrlLevy.Barrier.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:21.979016+00:00
-- url     : https://prove2.me/theorems/0f9d1620-ba08-43c0-9595-47d8de25a2c8
-- title:
--   Lemma 8, p. 13 — v_{b*} is convex and C¹, with v′_{b*} = E_x[∫ e^{−qt} f′_{ε*}(U^{b*}_t) dt] and smooth fit v′_{b*} = −C on (−∞, b*]
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, the function $x\mapsto v_{b^*}(x)$ is convex and belongs to $C^1(\mathbb R)$. Moreover there is a single $\varepsilon^*\in[0,1]$, the same for every $x$, such that, writing $f'_{\varepsilon^*}(y)=(1-\varepsilon^*)f'_+(y)+\varepsilon^*f'_-(y)$,
--   $$v'_{b^*}(x)=\mathbb E_x\Big[\int_0^\infty e^{-qt}f'_{\varepsilon^*}(U^{b^*}_t)\,dt\Big]\qquad\text{for all }x\in\mathbb R ,$$
--   and in particular $v'_{b^*}(x)=-C$ for $x\in(-\infty,b^*]$.
--
--   The last identity is the smooth-fit condition; it is condition (4.30) of the verification lemma for $w=v_{b^*}$.
--
--   **Formalization Note** $\varepsilon^*$ is quantified once, before $x$, as the paper says it is invariant to $x$. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 13, Lemma 8

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP) :
    ConvexOn ℝ Set.univ (fun x => vb P X f q C x (bstar P X f q C)) ∧
      ContDiff ℝ 1 (fun x => vb P X f q C x (bstar P X f q C)) ∧
      ∃ εs : ℝ, εs ∈ Set.Icc (0 : ℝ) 1 ∧
        (∀ x, deriv (fun y => vb P X f q C y (bstar P X f q C)) x =
          ∫ ω, (∫ t in Set.Ici (0 : ℝ), Real.exp (-q * t) *
            ((1 - εs) * rd f (U X x (barrierR X x (bstar P X f q C)) t.toNNReal ω)
              + εs * ld f (U X x (barrierR X x (bstar P X f q C)) t.toNNReal ω))) ∂P) ∧
        ∀ x, x ≤ bstar P X f q C →
          deriv (fun y => vb P X f q C y (bstar P X f q C)) x = -C := by sorry

end SingCtrlLevy.Barrier

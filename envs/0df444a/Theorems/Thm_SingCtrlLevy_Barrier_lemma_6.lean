-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_6
-- name    : SingCtrlLevy.Barrier.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:28.640673+00:00
-- url     : https://prove2.me/theorems/9378e764-3008-4111-86f8-4550cadb6199
-- title:
--   Lemma 6, p. 8 — continuity of b ↦ v_b(x) and its right derivative (3.11) via τ⁻_b
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, fix a starting point $x\in\mathbb R$, and let $\tau^-_b=\inf\{t>0:X_t<b\}$ under $\mathbb P_x$ (with $e^{-q\tau^-_b}=0$ when $\tau^-_b=\infty$).
--
--   1. $b\mapsto v^{(1)}_b(x)$ is continuous on $\mathbb R$, and for $b\neq x$
--   $$\lim_{\varepsilon\downarrow0}\frac{v^{(1)}_{b+\varepsilon}(x)-v^{(1)}_b(x)}{\varepsilon}=\mathbb E_x\Big[\int_{\tau^-_b}^\infty e^{-qt}f'_+(U^b_t)\,dt\Big].$$
--   2. $b\mapsto v^{(2)}_b(x)$ is continuous on $\mathbb R$, and for $b\neq x$
--   $$\lim_{\varepsilon\downarrow0}\frac{v^{(2)}_{b+\varepsilon}(x)-v^{(2)}_b(x)}{\varepsilon}=\mathbb E_x\big[e^{-q\tau^-_b}\big].$$
--   3. $b\mapsto v_b(x)$ is continuous on $\mathbb R$, and for $b\neq x$
--   $$\lim_{\varepsilon\downarrow0}\frac{v_{b+\varepsilon}(x)-v_b(x)}{\varepsilon}=\mathbb E_x\Big[\int_{\tau^-_b}^\infty e^{-qt}f'_+(U^b_t)\,dt\Big]+C\,\mathbb E_x\big[e^{-q\tau^-_b}\big]\qquad(3.11).$$
--
--   These right derivatives in the barrier are the paper's key tool for comparing barrier strategies.
--
--   **Formalization Note** The time integral over $[\tau^-_b,\infty)$ is taken over $\{t\ge0:\tau^-_b\le t\}$, empty when $\tau^-_b=\infty$. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 8, Lemma 6 (i)–(iii), (3.11)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (x : ℝ) :
    (Continuous (fun b => vb1 P X f q x b) ∧
      ∀ b, b ≠ x → Tendsto (fun ε => (vb1 P X f q x (b + ε) - vb1 P X f q x b) / ε) (𝓝[>] 0)
        (𝓝 (∫ ω, (∫ t in {t : ℝ | 0 ≤ t ∧ tauMinus X x b ω ≤ ENNReal.ofReal t},
          Real.exp (-q * t) * rd f (U X x (barrierR X x b) t.toNNReal ω)) ∂P))) ∧
    (Continuous (fun b => vb2 P X q x b) ∧
      ∀ b, b ≠ x → Tendsto (fun ε => (vb2 P X q x (b + ε) - vb2 P X q x b) / ε) (𝓝[>] 0)
        (𝓝 (∫ ω, expDisc q (tauMinus X x b ω) ∂P))) ∧
    (Continuous (fun b => vb P X f q C x b) ∧
      ∀ b, b ≠ x → Tendsto (fun ε => (vb P X f q C x (b + ε) - vb P X f q C x b) / ε) (𝓝[>] 0)
        (𝓝 ((∫ ω, (∫ t in {t : ℝ | 0 ≤ t ∧ tauMinus X x b ω ≤ ENNReal.ofReal t},
          Real.exp (-q * t) * rd f (U X x (barrierR X x b) t.toNNReal ω)) ∂P)
          + C * ∫ ω, expDisc q (tauMinus X x b ω) ∂P))) := by sorry

end SingCtrlLevy.Barrier

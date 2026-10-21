-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_14
-- name    : SingCtrlLevy.Barrier.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:25.065156+00:00
-- url     : https://prove2.me/theorems/567ab618-7216-456d-ae17-45426105c6db
-- title:
--   Lemma 14, p. 19 — b*_(ε) ↓ b* as ε ↓ 0
-- statement:
--   Let $X$ have unbounded variation paths, and let Assumptions 1 and 2 and $q>0$ hold. For $\varepsilon>0$ let
--   $$\rho^{(\varepsilon)}(b)=\mathbb E_b\Big[\int_0^\infty e^{-qt}f^{(\varepsilon)\prime}(U^b_t)\,dt\Big],\qquad b^*_{(\varepsilon)}=\inf\{b\in\mathbb R:\rho^{(\varepsilon)}(b)+C\ge0\},$$
--   with $f^{(\varepsilon)\prime}$ from (4.35). Then $b^*_{(\varepsilon)}\downarrow b^*$ as $\varepsilon\downarrow0$: the map $\varepsilon\mapsto b^*_{(\varepsilon)}$ is nondecreasing on $(0,\infty)$ and
--   $$\lim_{\varepsilon\downarrow0}b^*_{(\varepsilon)}=b^* .$$
--
--   **Formalization Note** "$\downarrow$ as $\varepsilon\downarrow0$" is formalized as monotonicity in $\varepsilon$ on $(0,\infty)$ plus the right limit at $0$. (The paper's proof calls $\varepsilon\mapsto b^*_{(\varepsilon)}$ "decreasing", but by (4.38) $f^{(\varepsilon)\prime}$ increases as $\varepsilon$ decreases, so $b^*_{(\varepsilon)}$ decreases with $\varepsilon$, as the statement says.) The hypothesis of unbounded variation is the scope of §4.2. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 19, Lemma 14 (ρ^(ε), b*_(ε) defined p. 19)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (hUBV : ¬ T.BoundedVariation) :
    MonotoneOn (fun ε => bstarOf P X q C (fEpsDeriv f ε)) (Set.Ioi 0) ∧
      Tendsto (fun ε => bstarOf P X q C (fEpsDeriv f ε)) (𝓝[>] 0) (𝓝 (bstar P X f q C)) := by sorry

end SingCtrlLevy.Barrier

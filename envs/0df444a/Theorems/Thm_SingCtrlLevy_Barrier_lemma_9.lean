-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_9
-- name    : SingCtrlLevy.Barrier.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:28.829848+00:00
-- url     : https://prove2.me/theorems/7279fc02-4608-47e0-845c-76aaee30b92f
-- title:
--   Lemma 9, p. 13 — under Assumption 3 (unbounded variation), v_{b*} ∈ C² ⊂ C²_poly
-- statement:
--   Let $X$ have unbounded variation paths and, in addition to Assumptions 1 and 2 and $q>0$, let Assumption 3 hold: $f\in C^2(\mathbb R)$ and $f''$ has polynomial growth. Then $v_{b^*}$ belongs to $C^2(\mathbb R)$, and hence (with Lemma 3 and (3.7)) to
--   $$C^2_{\mathrm{poly}}=\{g\in C^2(\mathbb R):|g(x)|<b_1|x|^M+b_2\ \text{for some }b_1,b_2>0,\ M\in\mathbb N\}.$$
--
--   This is the smoothness the verification lemma needs in the unbounded-variation case.
--
--   **Formalization Note** The statement carries the hypothesis that $X$ has unbounded variation. Assumption 3 constrains $f$ only in that case, and the paper's proof (Appendix A.6, p. 30) uses that $f$ is differentiable "by assumption"; in the bounded-variation case the verification lemma needs only $C^1_{\mathrm{poly}}$, which Lemmas 3 and 8 give. The conclusion is membership in $C^2_{\mathrm{poly}}$, which includes $C^2$. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 13, Lemma 9 (proof: Appendix A.6, p. 30)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (hUBV : ¬ T.BoundedVariation) (hA3 : Assumption3 T f) :
    CPoly 2 (fun x => vb P X f q C x (bstar P X f q C)) := by sorry

end SingCtrlLevy.Barrier

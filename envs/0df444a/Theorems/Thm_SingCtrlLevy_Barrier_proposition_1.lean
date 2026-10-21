-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_proposition_1
-- name    : SingCtrlLevy.Barrier.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:37.400055+00:00
-- url     : https://prove2.me/theorems/9d123beb-9188-4a67-8287-430c8b1307ba
-- title:
--   Proposition 1 (verification lemma), p. 14 — (L − q)w + f ≥ 0 and w′ + C ≥ 0 imply w ≤ v
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, suppose that $X$ has bounded (resp. unbounded) variation paths and let $w:\mathbb R\to\mathbb R$ belong to $C^1_{\mathrm{poly}}$ (resp. $C^2_{\mathrm{poly}}$) and satisfy, for all $x\in\mathbb R$,
--   $$(\mathcal L-q)w(x)+f(x)\ge0\quad(4.29),\qquad w'(x)+C\ge0\quad(4.30).$$
--   Then $w(x)\le v(x)$ for all $x\in\mathbb R$; that is, $w(x)\le v_\pi(x)$ for every starting point $x$ and every strategy $\pi$ admissible from $x$.
--
--   This is the sufficient condition through which the candidate $v_{b^*}$ is shown to be the value function.
--
--   **Formalization Note** $w\le v=\inf_\pi v_\pi$ is stated equivalently as $w(x)\le v_\pi(x)$ for every admissible $\pi$, which avoids the infimum. $(\mathcal L-q)w(x)$ is written out as $\mathcal Lw(x)-qw(x)$. In the bounded-variation case $\sigma=0$, so $\mathcal L$ uses only $w'$. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 14, Proposition 1, (4.29)–(4.30)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (w : ℝ → ℝ)
    (hw : (T.BoundedVariation → CPoly 1 w) ∧ (¬ T.BoundedVariation → CPoly 2 w))
    (h429 : ∀ x, 0 ≤ gen T w x - q * w x + f x)
    (h430 : ∀ x, 0 ≤ deriv w x + C) :
    ∀ (x : ℝ) (R : ℝ≥0 → Ω → ℝ), IsAdmissible P X f q x R → w x ≤ cost P X f q C x R := by sorry

end SingCtrlLevy.Barrier

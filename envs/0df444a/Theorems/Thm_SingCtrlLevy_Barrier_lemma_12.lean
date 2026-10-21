-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_12
-- name    : SingCtrlLevy.Barrier.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:31.938557+00:00
-- url     : https://prove2.me/theorems/e6b602d9-e23a-4c31-930a-ade70980b883
-- title:
--   Lemma 12, p. 18 — the smoothed cost f^(ε) is C² with f^(ε)″ of polynomial growth (Assumption 3)
-- statement:
--   Let $f$ and $C$ satisfy Assumption 1 (for some $q$), let $\varepsilon>0$, and define
--   $$f^{(\varepsilon)\prime}(x)=\frac1{\varepsilon^2}\int_{-\varepsilon}^0dz\int_{-\varepsilon}^0f'_+(x+y+z)\,dy\quad(4.35),\qquad f^{(\varepsilon)}(x)=f(b)+\int_b^xf^{(\varepsilon)\prime}(y)\,dy .$$
--   Then $f^{(\varepsilon)}$ satisfies Assumption 3: $f^{(\varepsilon)}\in C^2(\mathbb R)$, and its second derivative has polynomial growth, $|f^{(\varepsilon)\prime\prime}(x)|\le k_1+k_2|x|^N$ for some $k_1,k_2$, $N\in\mathbb N$.
--
--   This lets the results of §4.1, proved under Assumption 3, be applied to the smoothed cost $f^{(\varepsilon)}$.
--
--   **Formalization Note** The paper anchors $f^{(\varepsilon)}$ at $b=b^*$; the statement is made for every anchor $b\in\mathbb R$, which contains the paper's case (the anchor only adds a constant). Assumption 3's content is stated directly (it does not involve the process).
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 18, Lemma 12 (definitions p. 17, (4.35))

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_12 (f : ℝ → ℝ) (q C : ℝ) (hA1 : Assumption1 f C q) (b ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (fEps f b ε) ∧
      ∃ k₁ k₂ : ℝ, ∃ N : ℕ, ∀ x, |iteratedDeriv 2 (fEps f b ε) x| ≤ k₁ + k₂ * |x| ^ N := by sorry

end SingCtrlLevy.Barrier

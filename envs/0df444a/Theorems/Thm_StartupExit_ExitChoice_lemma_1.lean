-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_1
-- name    : StartupExit.ExitChoice.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:01.721782+00:00
-- url     : https://prove2.me/theorems/4a0c401f-0ba6-45d4-b912-1219e4dbe4a7
-- title:
--   Lemma 1, pp. 11–12 — highest and second-highest of z uniform draws on [−1, 1]: F = Hᶻ, G = zHᶻ⁻¹ − (z−1)Hᶻ, densities f, g
-- statement:
--   Let $v_1,\dots,v_z$ be independent, each uniform on $[-1,1]$ with distribution function $H(x)=(x+1)/2$ and density $h=1/2$. For every $x\in[-1,1]$:
--
--   1. if $z\ge1$, the probability that the highest draw is at most $x$ is
--   $$P\bigl(\max_i v_i\le x\bigr)=F(x,z)=H(x)^z;$$
--   2. if $z\ge2$, the probability that the second-highest draw is at most $x$, i.e. that at most one draw exceeds $x$, is
--   $$G(x,z)=zH(x)^{z-1}-(z-1)H(x)^z;$$
--   3. for $x\in(-1,1)$, the densities are the derivatives: $\frac{\partial}{\partial x}F(x,z)=f(x,z)=zH(x)^{z-1}h(x)$ for $z\ge1$, and $\frac{\partial}{\partial x}G(x,z)=g(x,z)=z(z-1)H(x)^{z-2}(1-H(x))h(x)$ for $z\ge2$.
--
--   This lemma identifies the closed forms used throughout the model with the actual order statistics of the buyers' valuations.
--
--   **Formalization Note** Probabilities are computed under the product measure $\mu^{\otimes z}$ on $\mathbb R^{\mathrm{Fin}\,z}$, valued in $[0,\infty]$, and compared with `ENNReal.ofReal` of the closed form. The event "second highest $\le x$" is written as "the number of coordinates $>x$ is at most one".
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), pp. 11–12 (PDF 12–13), Lemma 1

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_OrderStats

open MeasureTheory

namespace StartupExit.ExitChoice

theorem lemma_1 (z : ℕ) :
    (1 ≤ z → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Measure.pi (fun _ : Fin z => unifMeasure) {v : Fin z → ℝ | ∀ i, v i ≤ x} =
        ENNReal.ofReal (Fcdf x z)) ∧
    (2 ≤ z → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Measure.pi (fun _ : Fin z => unifMeasure)
          {v : Fin z → ℝ | (Finset.univ.filter (fun i => x < v i)).card ≤ 1} =
        ENNReal.ofReal (Gcdf x z)) ∧
    (1 ≤ z → ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun y => Fcdf y z) (fdens x z) x) ∧
    (2 ≤ z → ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun y => Gcdf y z) (gdens x z) x) := by sorry

end StartupExit.ExitChoice

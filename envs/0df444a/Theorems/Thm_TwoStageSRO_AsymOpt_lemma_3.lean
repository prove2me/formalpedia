-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_lemma_3
-- name    : TwoStageSRO.AsymOpt.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:34.109178+00:00
-- url     : https://prove2.me/theorems/2a0d85e4-39d2-4c0c-8ab8-5404dc22039b
-- title:
--   Lemma 3, p. 17 — Q^C_ϵ(x,ζ) ≤ Q(x*,ζ) + ϵη^C + L‖x − x*‖_* on Ξ*
-- statement:
--   Under [A2]–[A3], fix an optimal first-stage decision $x^*$ and let $\Xi^*=\{\zeta\in\Xi:\exists y,\ Tx^*+Wy\ge h(\zeta)\}$. Let $D=\{\delta\in\mathbb R^m: W^\top\delta=q,\ \delta\ge0\}$. Let $x\in\mathbb R^n$, $\mathcal C\subseteq\mathbb R^{r\times d}$ and $\epsilon\ge0$ satisfy $Q^{\mathcal C}_\epsilon(x,\zeta)<\infty$ for all $\zeta\in\Xi^*$. Then
--   $$Q^{\mathcal C}_\epsilon(x,\zeta)\le Q(x^*,\zeta)+\epsilon\,\eta^{\mathcal C}+L\,\|x-x^*\|_*\qquad\text{for all }\zeta\in\Xi^*,$$
--   where
--   $$\eta^{\mathcal C}=\sup_{Y\in\mathcal C,\ \delta\in\mathrm{ext}(D)}\Big\{\|Y^\top q\|_*+\sum_{j=1}^m\delta_j\|h_j-Y^\top w_j\|_*\Big\},\qquad L=\max_{\delta\in\mathrm{ext}(D)}\|T^\top\delta\|,$$
--   and $h_j^\top$, $w_j^\top$ are the $j$-th rows of $H$ and $W$.
--
--   The bound controls the gap between the cost of the multi-policy approximation and the true second-stage cost, uniformly over $\Xi^*$; it vanishes as $\epsilon\to0$ and $x\to x^*$.
--
--   **Formalization Note** The law is supported on $\Xi$; [A2]–[A3] and optimality of $x^*$ are the standing assumptions of §4.2. [A2] implies $D\ne\emptyset$ (footnote 3, p. 17). The inequality is in `EReal`: $\eta^{\mathcal C}$ is an extended supremum ($+\infty$ for unbounded $\mathcal C$, which makes the bound trivial when $\epsilon>0$) and $0\cdot(+\infty)=0$ at $\epsilon=0$. Both $\|\cdot\|$ and $\|\cdot\|_*$ on $\mathbb R^n$ are for the same $\ell_p$-norm as the balls.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 17, Lemma 3

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 17, Lemma 3:
let `x ∈ ℝⁿ`, `C ⊆ ℝ^{r×d}` and `ε ≥ 0` satisfy `Q^C_ε(x, ζ) < ∞` for all `ζ ∈ Ξ*`; then
`Q^C_ε(x, ζ) ≤ Q(x*, ζ) + εη^C + L‖x − x*‖_*` for all `ζ ∈ Ξ*`.

**Formalization Note** `x*` is `xs`, optimal for (OPT) under §4.2's standing [A2]–[A3], and
`Ξ* = XiStar M xs`. [A2] implies `D ≠ ∅` (footnote 3, p. 17). The bound is in `EReal`: `η^C` (`etaC`) is an
`EReal` supremum, `+∞` for unbounded `C`, and `0 · (+∞) = 0` at `ε = 0`. `L` is `Lconst` and
`‖·‖_*` is `dualNorm`, both on `ℝⁿ` for the same `ℓp`-norm. -/
theorem lemma_3 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (x : Fin n → ℝ) (C : Set (Matrix (Fin r) (Fin d) ℝ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hfeas : ∀ ζ ∈ XiStar M xs, QC M p C ε x ζ < ⊤) :
    ∀ ζ ∈ XiStar M xs,
      QC M p C ε x ζ ≤
        Q M xs ζ + (ε : EReal) * etaC M p C + ((Lconst M p * dualNorm p (x - xs) : ℝ) : EReal) := by sorry

end TwoStageSRO.AsymOpt

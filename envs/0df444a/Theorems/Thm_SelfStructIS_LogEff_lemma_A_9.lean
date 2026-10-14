-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_9
-- name    : SelfStructIS.LogEff.lemma_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:10.453265+00:00
-- url     : https://prove2.me/theorems/1481e54e-5936-426a-bfb6-4ddc8594c829
-- title:
--   Lemma A.9, pp. 34–35 (support-restricted) — lev⁺₁(Lᵤ) avoids a ball B_γ around 0
-- statement:
--   Suppose $X$ satisfies Assumption 3.1 and $L$ satisfies Assumption 2.1. Then there is $\gamma>0$ such that, for all sufficiently large $u$, every $p\in\mathbb R^d_{++}$ with $q(t(u)p)\in\operatorname{supp}(X)$ and $L_u(p)\ge1$ satisfies $\|p\|_\infty>\gamma$:
--   $$\mathrm{lev}^+_1(L_u)\cap\{p: q(t(u)p)\in\operatorname{supp}(X)\}\subseteq\mathbb R^d_+\setminus B_\gamma .$$
--
--   In the standardized coordinates the rare set stays a fixed distance away from the origin, which is what makes the Laplace-type functional of Lemma A.6 decay at the rate $I^*$.
--
--   **Formalization Note** As printed (without the restriction to $q(t(u)p)\in\operatorname{supp}(X)$) the lemma can fail: Assumption 2.1 does not constrain $L$ outside $\operatorname{supp}(X)\cup\mathbb R^d_+$, so when the joint support omits a negative orthant that the marginal quantiles reach, $L$ may be large there and $\mathrm{lev}^+_1(L_u)$ meets every $B_\gamma$. The proof of Theorem 5.1 uses the lemma only at $p=Y_u$, which lies in that set almost surely, so the restriction is harmless; the paper's own Lemma A.1 carries the same $\cap\operatorname{supp}(X)$. $\gamma$ is chosen before $u$, as in the proof.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, pp. 34–35, Lemma A.9

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_9 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (L Lstar : (Fin d → ℝ) → ℝ) (ρ : ℝ) (h21 : Assumption21 μ L ρ Lstar) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ u in atTop, ∀ q : Fin d → ℝ, (∀ i, 0 < q i) →
      qvec μ (tfun μ ρ u • q) ∈ μ.support → 1 ≤ Lu μ L ρ u q → γ < ‖q‖ := by sorry

end SelfStructIS.LogEff

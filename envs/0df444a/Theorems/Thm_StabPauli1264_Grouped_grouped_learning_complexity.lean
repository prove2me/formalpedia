-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_grouped_learning_complexity
-- name    : StabPauli1264.Grouped.grouped_learning_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:22.525541+00:00
-- url     : https://prove2.me/theorems/86e43436-2402-4aa5-ba27-be7560b36c10
-- title:
--   Theorem 2.3 — Optimal grouped learning complexity
-- statement:
--   For every nonempty signed Pauli window $M$, every known real evaluation distribution $p$, and every $0<\varepsilon,\delta<1$, Algorithm 1 returns a proper stabilizer tableau. On every input density matrix $\rho$, its output $\widehat\sigma$ satisfies
--
--   $$\Pr\!\left[R_{p,\rho}(f_{\widehat\sigma})-R^*_{p,\rho}\le\varepsilon\right]\ge1-\delta.$$
--
--   It uses at most $\lfloor2/\varepsilon\rfloor$ settings and at most
--
--   $$N_{\rm tot}\le\left\lceil\frac{4(c_0+\sqrt{2\ln(1/\delta)})^2}{\varepsilon^2}\right\rceil+\lfloor2/\varepsilon\rfloor,\quad c_0=2\sqrt{\ln2}\sum_{s=0}^\infty2^{-s/2}\sqrt{s+1}.$$
--
--   The series is summable. For every fixed $0<\varepsilon_0,\delta_0<1/2$, there are positive constants $B,C$ depending only on these cutoffs such that, simultaneously for every nonempty window and $0<\varepsilon\le\varepsilon_0$, $0<\delta\le\delta_0$,
--
--   $$B\frac{\ln(1/\delta)}{\varepsilon^2}\le N_{\rm coll}(M,\varepsilon,\delta)\le N_{\rm grouped}(M,\varepsilon,\delta)\le C\frac{\ln(1/\delta)}{\varepsilon^2}.$$
--
--   Both complexities are worst case over $p$ for a fixed window. The statement fixes the admissible lower coefficient $B=B_{\varepsilon_0,\delta_0}$ from Eq. (31) and the upper coefficient $C=16+(8c_0^2+\varepsilon_0^2+2\varepsilon_0)/\ln(1/\delta_0)$ obtained from the exact copy bound. With $a=1+1/(2\varepsilon_0)$, $\bar\mu=\varepsilon_0+1/2$ and $A=(1-2\delta_0)(1+\ln(1-\delta_0)/\ln(1/\delta_0))$, the former is $(1-\bar\mu^2)A/(2a^2)$. Neither coefficient depends on $n,m,M,p,\varepsilon,\delta$. The sharp algorithm bound is retained separately. This is the complete grouped and collective statistical result; classical computation is unrestricted.
--
--   Differences from the source:
--   - encoding: arbitrary tie breaking and n signed stabilizer generators → fixed deterministic exact-maximizer ties and valid tableaux on Fin n; reason: every allowed source tie rule is valid; this fixes one without target dependence
--   - encoding: convergent infinite series defining c_0 → real tsum together with summability in the conclusion; reason: the series is exact and its default value on a nonsummable series cannot discharge the goal
--   - generalization: two Theta claims with constants depending only on the cutoffs → a uniform chain of extended-natural complexity bounds with explicit B from Eq. (31) and explicit C derived from Eq. (7); reason: the Lean conclusion fixes B to the Eq. (31) constant of the source and C to 16+(8c_0^2+ε_0^2+2ε_0)/ln(1/δ_0), which the source does not state; it implies the Θ claims of the source (take these B,C), and C is valid because ⌈x⌉≤x+1, (c_0+√(2L))^2≤2c_0^2+4L, ⌊2/ε⌋≤2/ε, ε^2+2ε≤ε_0^2+2ε_0 and L=ln(1/δ)≥ln(1/δ_0)
--   - encoding: least feasible integer copy count → extended-natural infimum with infinity for an empty feasible set; reason: nonempty subsets of naturals attain their least element; comparison with real coefficients preserves infinity
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Theorem 2.3 Eq. (7), p. 6; Algorithm 1 p. 7; proof pp. 20–22; lower coefficient §7 Eq. (31), p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Complexity
set_option autoImplicit false

namespace StabPauli1264.Grouped

/-- Full Theorem 2.3, p.6, Algorithm 1 p.7, proofs pp.20--22 and Eq.(31).
Constants are quantified before n, m, M, epsilon and delta. -/
theorem grouped_learning_complexity :
    Summable c0Term ∧
    (∀ {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      GroupedPermitted M (peelingLearner M p ε δ) ∧
      (peeled M p ε).length ≤ ⌊2 / ε⌋₊ ∧
      (schedule M p ε δ).length ≤ copyBudget ε δ + ⌊2 / ε⌋₊ ∧
      ∀ ρ : Density n, 1 - δ ≤ groupedSuccess M p (peelingLearner M p ε δ) ρ.matrix ε) ∧
    (∀ ε₀ δ₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 → 0 < δ₀ → δ₀ < 1 / 2 →
      ∃ B C : ℝ, B = lowerConstant ε₀ δ₀ ∧ C = upperConstant ε₀ δ₀ ∧
      0 < B ∧ 0 < C ∧
      ∀ {n m : ℕ} (M : Window n m) (ε δ : ℝ),
        0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ →
        ENNReal.ofReal (B * Real.log (1 / δ) / ε ^ 2) ≤
          countReal (collectiveComplexity M ε δ) ∧
        collectiveComplexity M ε δ ≤ groupedComplexity M ε δ ∧
        countReal (groupedComplexity M ε δ) ≤
          ENNReal.ofReal (C * Real.log (1 / δ) / ε ^ 2)) := by sorry

end StabPauli1264.Grouped

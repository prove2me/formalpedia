-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_single_dyadic_class_estimate
-- name    : StabPauli1264.Grouped.single_dyadic_class_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:18.19933+00:00
-- url     : https://prove2.me/theorems/58141a42-95d7-4cec-85c4-a338fb54ebb6
-- title:
--   Lemma 8.2 — Single dyadic class estimate
-- statement:
--   Let $M$ be a window, $p$ its known evaluation distribution and $\rho$ any density matrix. Consider disjoint commuting measured contexts $C_j$ with $N_j\ge1$ independent fresh copies each. Within-copy outcomes have the actual joint Born law and need not have independent coordinates. Write $I=\bigcup_j C_j$, $q=p(I)>0$, $\sigma^2=\max_j N_j^{-1}$ and $\nu_i=\widehat b_i-b_i$.
--
--   For every real $x$ with $0<x\le q$, the capped-weight maximum is attained and satisfies
--
--   $$\mathbb E\max\left\{\sum_{i\in I}y_i|\nu_i|:0\le y_i\le p_i,\ \sum_{i\in I}y_i=x\right\}\le x\sigma\sqrt{2\ln(2q/x)}.$$
--
--   The expectation uses the physical product law of the fresh outcome vectors. This bound applies to every class and every feasible mass, including the later choice $x=\min\{2^{-s},q\}$.
--
--   Differences from the source:
--   - encoding: finite class indexed by J_s → class reindexed by Fin l, with J equal to the full index set; reason: bijection of the same finitely many measured contexts changes no experiment
--   - encoding: maximum over the capped-weight polytope → real supremum together with explicit attainment for every transcript; reason: the displayed maximum and its expectation are recovered without adding a compactness hypothesis
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 8.2 Eq. (50) and expectation bound, pp. 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Estimation
set_option autoImplicit false

namespace StabPauli1264.Grouped

open scoped Classical

/-- Liu--Yang--Yang, Lemma 8.2, pp.20--21. Fin l indexes exactly the class J_s. -/
theorem single_dyadic_class_estimate {n m l : ℕ} (M : Window n m) (p : EvalLaw m)
    (ρ : Density n) (E : BlockExperiment m l)
    (hcontext : ∀ j, IsContext M (E.context j))
    (hdisjoint : Pairwise (fun j j' => Disjoint (E.context j) (E.context j')))
    (hcopies : ∀ j, 0 < E.copies j)
    (hq : 0 < mass p (classIndices E Finset.univ))
    (x : ℝ) (hx : 0 < x) (hxq : x ≤ mass p (classIndices E Finset.univ)) :
    (∀ h : BlockData E, ∃ y : Fin m → ℝ,
      ClassFeasible p (classIndices E Finset.univ) x y ∧
      classPhi M p E ρ.matrix Finset.univ x h = classObjective M E ρ.matrix Finset.univ h y) ∧
    classExpectation M p E ρ.matrix Finset.univ x ≤
      x * classSigma E Finset.univ *
        Real.sqrt (2 * Real.log (2 * mass p (classIndices E Finset.univ) / x)) := by sorry

end StabPauli1264.Grouped

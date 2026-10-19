-- Prove2me | Theorems.Thm_ParamMCF_MCA_lemma_4
-- name    : ParamMCF.MCA.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:17.127817+00:00
-- url     : https://prove2.me/theorems/f3f45159-1fc9-4cbd-836f-23f89a038b15
-- title:
--   Lemma 4, p. 16 — close marginal costs give an approximate flow function
-- statement:
--   Let $f_e$ be the original marginal costs and $\widetilde f_e$ a second family of continuous, strictly increasing, sign preserving marginal costs. Let $\alpha>1$, $\beta\ge0$, $\lambda^{\max}>0$, $x^{\max}>0$, and $m=|E|$. Suppose, on $[-x^{\max},x^{\max}]$ for every edge, either
--
--   $$|\widetilde f_e(x)-f_e(x)|\le\frac{\alpha-1}{1+\alpha}|f_e(x)|+\frac{\beta}{(1+\alpha)m x^{\max}},\tag{15}$$
--
--   or both $|\widetilde f_e(x)|\ge|f_e(x)|$ and
--
--   $$|\widetilde f_e(x)-f_e(x)|\le(\alpha-1)|f_e(x)|+\frac{\beta}{m x^{\max}}.\tag{16}$$
--
--   Then every minimum cost flow function for the $\widetilde f_e$ instance is $(\alpha,\beta)$ approximate for the original instance on $[0,\lambda^{\max}]$.
--
--   The lemma transfers pointwise marginal cost control to a whole parametric flow function.
--
--   **Formalization Note** The alternative is global across all edges. The second family is explicitly continuous, strictly increasing, and sign preserving, as needed for the paper's edge flow bound. The extra condition $x^{\max}>0$ makes the displayed quotients meaningful. Costs use $\int_0^x$ and the directed or undirected case of (14).
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 16, Lemma 4, (15), (16)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- Lemma 4, p. 16, for base-zero costs and the directed/undirected cases. -/
theorem lemma_4 {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f ft : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hft : ∀ e, IsContinuousMarginalCost (ft e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (hclose :
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |ft e x - f e x| ≤
          (alpha - 1) / (1 + alpha) * |f e x| +
            beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax)) ∨
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |f e x| ≤ |ft e x| ∧
          |ft e x - f e x| ≤
            (alpha - 1) * |f e x| +
              beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax)))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed ft (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt := by sorry

end ParamMCF.MCA

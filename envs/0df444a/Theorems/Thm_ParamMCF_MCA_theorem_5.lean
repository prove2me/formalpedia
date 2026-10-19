-- Prove2me | Theorems.Thm_ParamMCF_MCA_theorem_5
-- name    : ParamMCF.MCA.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:13.088962+00:00
-- url     : https://prove2.me/theorems/cf17d18f-e7cc-4227-bc77-9c3a5eb03666
-- title:
--   Theorem 5, pp. 17–18 (corrected) — spline mesh conditions for approximate minimum cost flow
-- statement:
--   Consider a finite strongly connected directed network with balanced demands $b^0+\lambda b$ and strictly increasing marginal costs $f_e$ that are differentiable three times. Let $\alpha>1$, $\beta\ge0$, $\lambda^{\max}>0$, $x^{\max}>0$, $m=|E|$, and give each edge a strictly increasing mesh from $-x^{\max}$ to $x^{\max}$ that contains zero. Write $\delta_i=x_{i+1}-x_i$ and $s_{f_e}$ for the chord spline.
--
--   If all edge intervals satisfy
--
--   $$\delta_i\sqrt{\max_{\xi\in[x_i,x_{i+1}+\delta_i]}|f_e''(\xi)|}\le2\sqrt2\sqrt{\frac{\alpha-1}{1+\alpha}\min\{|f_e(x_i)|,|f_e(x_{i+1})|\}+\frac{\beta}{(1+\alpha)m x^{\max}}},\tag{i}$$
--
--   or if $f_e''$ is nondecreasing and nonnegative on $[0,\infty)$ and nonincreasing and nonpositive on $(-\infty,0)$ and all intervals satisfy
--
--   $$\delta_i\max\{\sqrt{|f_e''(x_i)|},\sqrt{|f_e''(x_{i+1})|}\}\le2\sqrt2\sqrt{(\alpha-1)|f_e(x_i)|+\frac{\beta}{m x^{\max}}},\tag{ii}$$
--
--   then every minimum cost flow function for the spline instance is $(\alpha,\beta)$ approximate for the original instance on $[0,\lambda^{\max}]$.
--
--   This is the marginal cost approximation guarantee of the paper.
--
--   **Formalization Note** The printed theorem is false for meshes that skip zero. The corrected statement requires zero as a mesh point, uses the smaller endpoint magnitude in (i), and takes square roots of both second derivative terms in the factor $B$ of (ii). The hypothesis $x^{\max}>0$ is added because both step-size bounds divide by $x^{\max}$; without it the zero-demand instance with a one-point mesh is a counterexample. The shape condition in (ii) is kept as printed; with the stated differentiability it forces $f_e''=0$ on the negative half line. Edge costs are based at zero, the spline's end chords extend linearly, and only the directed and undirected cases are represented. The optimal cost uses the original $f_e$.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, pp. 17–18, Theorem 5 (labelled corrected)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- Theorem 5, pp. 17–18, labelled corrected: 0 is a mesh point, (i) uses the endpoint value
nearest 0, and `B` takes square roots of both terms; `0 < xmax` is added because both
step-size bounds divide by `xmax`. -/
theorem theorem_5 {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hf3 : ∀ e, Differentiable ℝ (deriv (f e)) ∧
      Differentiable ℝ (deriv (deriv (f e))))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (K : E → ℕ) (xs : (e : E) → Fin (K e + 1) → ℝ)
    (hxs : ∀ e, StrictMono (xs e))
    (hfirst : ∀ e, xs e 0 = -xmax b0 b lamMax)
    (hlast : ∀ e, xs e (Fin.last (K e)) = xmax b0 b lamMax)
    (hzero : ∀ e, ∃ j, xs e j = 0)
    (hstep :
      (∀ e (i : Fin (K e)),
        let xi := xs e i.castSucc
        let xn := xs e i.succ
        let delta := xn - xi
        delta * Real.sqrt
            (sSup ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc xi (xn + delta))) ≤
          2 * Real.sqrt 2 * Real.sqrt
            ((alpha - 1) / (1 + alpha) * min |f e xi| |f e xn| +
              beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax))) ∨
      ((∀ e,
          MonotoneOn (deriv (deriv (f e))) (Set.Ici 0) ∧
          (∀ x, 0 ≤ x → 0 ≤ deriv (deriv (f e)) x) ∧
          AntitoneOn (deriv (deriv (f e))) (Set.Iio 0) ∧
          (∀ x, x < 0 → deriv (deriv (f e)) x ≤ 0)) ∧
        ∀ e (i : Fin (K e)),
          let xi := xs e i.castSucc
          let xn := xs e i.succ
          let delta := xn - xi
          delta * max (Real.sqrt |deriv (deriv (f e)) xi|)
              (Real.sqrt |deriv (deriv (f e)) xn|) ≤
            2 * Real.sqrt 2 * Real.sqrt
              ((alpha - 1) * |f e xi| +
                beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax))))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed (fun e => linSpline (K e) (xs e) (f e))
        (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt := by sorry

end ParamMCF.MCA

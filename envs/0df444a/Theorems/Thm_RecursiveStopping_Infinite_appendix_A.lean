-- Prove2me | Theorems.Thm_RecursiveStopping_Infinite_appendix_A
-- name    : RecursiveStopping.Infinite.appendix_A
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:23.704351+00:00
-- url     : https://prove2.me/theorems/2ab5dc41-1de6-4055-8b7e-4105cf248770
-- title:
--   Appendix A — $(\mathcal A_d,\|\cdot\|_{\mathcal A_d})$ is complete and $\|\cdot\|_{\mathcal A_d}$ is a norm
-- statement:
--   For every dimension $d$:
--
--   1. $\|f\|_{\mathcal A_d}=0$ if and only if $f=0$, for every real function $f$ on $\mathbb R^d$;
--   2. $\|cf\|_{\mathcal A_d}=|c|\,\|f\|_{\mathcal A_d}$ for every $c\in\mathbb R$;
--   3. $\|f+g\|_{\mathcal A_d}\le\|f\|_{\mathcal A_d}+\|g\|_{\mathcal A_d}$;
--   4. every sequence $(f_n)\subset\mathcal A_d$ that is Cauchy for $\|f_m-f_n\|_{\mathcal A_d}$ converges in $\|\cdot\|_{\mathcal A_d}$ to a limit $f\in\mathcal A_d$.
--
--   Completeness of $\mathcal A_d$ is the setting for Banach's fixed-point theorem in the proof of Theorem 3.1.
--
--   **Formalization Note** The norm is $[0,\infty]$-valued, so 1–3 are stated for all real functions; with finite values they are the norm axioms on the functions of finite weighted norm.
--
--   Differences from the source:
--   - reading: $(\mathcal A_d,\|\cdot\|_{\mathcal A_d})$ is a Banach space → $\|\cdot\|_{\mathcal A_d}$ satisfies the norm axioms and $\mathcal A_d$ is complete for the metric $\|f-g\|_{\mathcal A_d}$; reason: $\mathcal A_d\subset C(\mathbb R^d;\mathbb R_+)$ by (8) is a cone, not a vector space
--   - generalization: $\|\cdot\|_{\mathcal A_d}$ is a norm (on $\mathcal A_d$) → the norm axioms for every real function on $\mathbb R^d$, with values in $[0,\infty]$; reason: restricted to functions of finite norm, in particular to $\mathcal A_d$ and differences of its elements, these are the source's norm axioms
--   - encoding: $\mathbb R^d$ with no bound on $d$ → `EuclideanSpace ℝ (Fin d)` for every $d\in\mathbb N$ (and $m=d-1\in\mathbb N$ in the finite horizon); reason: the Euclidean norm is $|\cdot|_d$; the source states no bound on $d$
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Appendix A, pp.31–32 (announced on p.8)

import Mathlib
import Definitions.Def_RecursiveStopping_Infinite_InA

open Filter Topology
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- Appendix A, Colaneri & De Angelis, arXiv:1905.02650v4, pp.31–32: "Here we show that
`(A_d, ∥·∥_{A_d})` is a Banach space. To start, we observe that `∥·∥_{A_d}` is a norm. To show
completeness of the space we consider a Cauchy sequence `(f_n) ⊂ A_d` …" (also p.8).

For every `d`:
1. `∥f∥_{A_d} = 0` iff `f = 0`, for every real function `f` on `ℝ^d`;
2. `∥c f∥_{A_d} = |c| ∥f∥_{A_d}` for every `c ∈ ℝ`;
3. `∥f + g∥_{A_d} ≤ ∥f∥_{A_d} + ∥g∥_{A_d}`;
4. completeness: every sequence `(f_n) ⊂ A_d` that is Cauchy for `∥f_m − f_n∥_{A_d}` converges in
   `∥·∥_{A_d}` to some `f ∈ A_d`.

**Formalization Note** `A_d` consists of non-negative functions, so it is a closed cone, not a
vector space; "Banach space" is read as: `∥·∥_{A_d}` is a norm (stated on all real functions,
with values in `[0, ∞]`) and `A_d` is complete for the metric `∥f − g∥_{A_d}`. -/
theorem appendix_A (d : ℕ) :
    (∀ f : EuclideanSpace ℝ (Fin d) → ℝ, wnorm f = 0 ↔ f = 0) ∧
    (∀ (c : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
      wnorm (fun x => c * f x) = ENNReal.ofReal |c| * wnorm f) ∧
    (∀ f g : EuclideanSpace ℝ (Fin d) → ℝ,
      wnorm (fun x => f x + g x) ≤ wnorm f + wnorm g) ∧
    (∀ fs : ℕ → EuclideanSpace ℝ (Fin d) → ℝ, (∀ n, InA (fs n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
        wnorm (fun x => fs m x - fs n x) < ENNReal.ofReal ε) →
      ∃ f, InA f ∧ Tendsto (fun n => wnorm (fun x => fs n x - f x)) atTop (𝓝 0)) := by sorry

end RecursiveStopping.Infinite

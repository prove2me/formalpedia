-- Prove2me | Theorems.Thm_RobustSAA_Convergence_proposition_9
-- name    : RobustSAA.Convergence.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:28.955153+00:00
-- url     : https://prove2.me/theorems/d6b8c12a-0312-4c1c-b057-2419a11044fa
-- title:
--   Proposition 9, p. 36 — under Assumption 1, convergence of C(x_N;𝓕_N) along convergent x_N → x gives (18)
-- statement:
--   Let $\mathcal G_N$ be any sequence of sets of distributions on $\Xi$, let $X$ and $c(x;\xi)$ satisfy the standing assumptions of §1.2 for the distribution $F$, and suppose Assumption 1 holds. Suppose that for every $x\in X$ and every sequence $x_N\in X$ with $x_N\to x$,
--   $$\mathcal C(x_N;\mathcal G_N)=\sup_{F_0\in\mathcal G_N}\mathbb E_{F_0}[c(x_N;\xi)]\longrightarrow\mathbb E_F[c(x;\xi)] .$$
--   Then condition (18) holds: for every compact $K\subseteq X$,
--   $$\sup_{x\in K}\big|\mathcal C(x;\mathcal G_N)-\mathbb E_F[c(x;\xi)]\big|\longrightarrow0 .$$
--
--   This is the deterministic half of the proof of (18): local uniform convergence is equivalent to convergence along convergent paths, and the "only if" side of Theorem 2 establishes the path version.
--
--   **Formalization Note** The statement is deterministic: it holds for every sequence of sets, and is applied to $\mathcal G_N=\mathcal F_N(\xi^1,\dots,\xi^N)$ for each sample path. The convergence is in the extended reals, so the hypothesis includes that $\mathcal C(x_N;\mathcal G_N)$ is eventually finite. The sequences $x_N$ and their limits are taken in $X$, the only place where (18) is asserted.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Proposition 9, §10.5, p. 36

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem proposition_9 {d dx : ℕ} {Ξ : Set (Pt d)} (F : ProbabilityMeasure ↥Ξ)
    (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ) (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ))
    (hS : Standing F X c) (hA1 : Assumption1 X c)
    (hconv : ∀ (xs : ℕ → Pt dx) (x : Pt dx), x ∈ X → (∀ N, xs N ∈ X) →
      Tendsto xs atTop (𝓝 x) →
        Tendsto (fun N => worstCase (𝒢 N) (c (xs N))) atTop (𝓝 ((trueObj F c x : ℝ) : EReal))) :
    ObjConv F X c 𝒢 := by sorry

end RobustSAA.Convergence

-- Prove2me | Theorems.Thm_WangMinimaxRegret_Reformulation_eq_3_4
-- name    : WangMinimaxRegret.Reformulation.eq_3_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:08.510934+00:00
-- url     : https://prove2.me/theorems/3ef576ba-c097-40af-aeee-b3519efe7068
-- title:
--   Section 2, equations (3)–(4) — no duality gap
-- statement:
--   Fix consistent nonnegative valuation data with arbitrary $K\ge0$, a feasible nondecreasing right-continuous normalized Stieltjes payment $m$, and a finite price $p\in I$. Let $V_3$ be the infimum of $\int m\,dH$ over finite nonnegative measures on $I$ satisfying the finite centered moment equations and $H([p,\infty))=1$. Let $D_4$ be the supremum of real $\theta$ for which real multipliers $\ell_1,\ldots,\ell_K$ satisfy
--   $$\sum_{k=1}^K(x^k-\mu_k)\ell_k\le m(x)\ (x\in I,\ x<p),\qquad \theta+\sum_{k=1}^K(x^k-\mu_k)\ell_k\le m(x)\ (x\in I,\ x\ge p).$$
--   The source assertion, retained here as printed, is
--   $$V_3=D_4,$$
--   and whenever $V_3$ equals a finite real $v$, there exist multipliers making $(v,\ell)$ dual feasible. This includes the finite-value attainment indicated by the displayed maximum. It assumes neither Slater regularity, positive variance, continuity of $m$, nor an existing dual optimizer. An infeasible primal has extended value $+\infty$, with no assertion of an infinite real maximizing variable. The claim is the duality step used before Theorem 1; the source counterexample is documented separately in INSIGHTS.yaml, not excluded by an added hypothesis.
--
--   Differences from the source:
--   - encoding: real interval, payment functions, probability laws, and moment orders 1 through K → real-line Borel measures supported on the interval, Stieltjes functions extended by zero below a and constantly above finite b, and Fin K exponents i+1; reason: extensions only fix values outside the domain; all atoms and payment jumps are retained, including the payment atom at a>0
--   - encoding: the seller knows moments of an actual valuation distribution → Consistent d requires a nonempty printed ambiguity class, with finite specified moments; reason: makes the standing information-consistency assumption explicit; no interiority, positive variance, or density is assumed
--   - encoding: nonnegative revenue integrals and optimization infima/suprema → nonnegative extended integrals and ENNReal/EReal extrema; zero-tail laws impose no fractional constraint; reason: avoids nonintegrable real integrals defaulting to zero and empty real extrema; empty infima are positive infinity
--   - encoding: real homogeneous moment integrals in (3) → finite H and integrable centered moment tests, omitting the identically zero order-zero row; reason: preserves the well-defined scalar rescaling domain of (3)
--   - reading: no duality gap and a displayed max in (4) → extended-value equality and dual attainment whenever the primal value is a finite real; reason: makes both the equality and maximum clauses explicit without assuming attainment
--   - reading: upper support endpoint b, used as infinity in later applications → b may be infinite, with all quantified valuations and prices finite; reason: no compactness or bounded-total-payment condition is added
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, p. 9, equation (4) and no-gap assertion referring to (3)

import Definitions.Def_WangMinimaxRegret_Reformulation_Programs

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace WangMinimaxRegret.Reformulation

theorem eq_3_4 (d : Data) (hc : Consistent d) (m : StieltjesFunction ℝ)
    (hm : IsPayment d m) (p : ℝ) (hp : p ∈ interval d) :
    ((homogenizedLP d m p).value : EReal) = dualValue d m p ∧
    (∀ v : ℝ, ((homogenizedLP d m p).value : EReal) = (v : EReal) →
      ∃ lam : Fin d.K → ℝ, DualFeasible d m p v lam) := by sorry

end WangMinimaxRegret.Reformulation

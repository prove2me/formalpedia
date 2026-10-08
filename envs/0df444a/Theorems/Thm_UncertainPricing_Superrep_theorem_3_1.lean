-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_theorem_3_1
-- name    : UncertainPricing.Superrep.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:59.16817+00:00
-- url     : https://prove2.me/theorems/27dcfa44-f073-4101-8070-b8e808070ae9
-- title:
--   Theorem 3.1, p. 11 — under H(μ̲, μ̄), Λ(f) = sup{E_P f : P ∈ P''} for the claims of Lemmas 5.4–5.6
-- statement:
--   Let $\Omega$ be the space of continuous paths on $[0,T]$ started at $0$, let $\underline\mu,\bar\mu$ be nonzero measures on $[0,T]$ with continuous distribution functions, $\bar\mu$ Hölder continuous, and let $\mathbf P$ be a set of martingale measures satisfying
--   $$d\underline\mu_t\le d\langle B\rangle^P_t\le d\bar\mu_t\qquad(P\in\mathbf P).$$
--   Let $\Lambda(f)=\inf\{a:\exists g\in K,\ a+g\ge f\text{ q.s.}\}$ be the superreplication price. Then there exists a set $\mathbf P''$ of martingale measures, each satisfying $H(\underline\mu,\bar\mu)$, such that
--   $$\Lambda(f)=\sup\{E_Pf:P\in\mathbf P''\}$$
--   for every bounded continuous claim $f$ of one of the forms
--   1. $f=F(B_{t_1},\dots,B_{t_d})$ with $F$ bounded continuous (cylindrical claims);
--   2. $f=G\big(\int_0^TF(B_s)\,ds\big)$ with $F$ continuous and $G$ bounded continuous;
--   3. $f=G(\sup_{t\in[0,T]}B_t)$ with $G$ bounded continuous.
--
--   The cheapest quasi-sure superreplication price of these path-dependent European claims is thus a supremum of expectations over a family of martingale laws obeying the same bracket bounds as the model family, a duality for the uncertain volatility model on a non-dominated set of laws.
--
--   **Formalization Note.** The page states the identity for $f\in\Gamma$, a class defined only in the proof (pp. 15, 22); here $\Gamma$ is replaced by the union of the three families that Lemmas 5.4–5.6 prove to lie in $\Gamma$ (the literal statement is the milestone `theorem_3_1_gamma`). Hölder continuity of $\bar\mu$ is the standing assumption of §4–§5 (p. 12: "From now on, we assume that $\bar\mu$ is Hölder continuous"; p. 20), which the theorem's statement does not repeat. $\Lambda$ and the supremum are in `EReal`, so an empty family gives $-\infty$, not a junk $0$.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Theorem 3.1, p. 11, with Lemmas 5.4–5.6, p. 22 (standing Hölder assumption pp. 12, 20)

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem theorem_3_1 (T : ℝ) (hT : 0 < T) (μL μU : StieltjesFunction ℝ) (hμL : IsDistFn T μL)
    (hμU : IsDistFn T μU) (Ps : Set (Measure (Ω T)))
    (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypLU μL μU P)
    (hHol : IsHolder T μU) :
    ∃ P'' : Set (Measure (Ω T)), (∀ P ∈ P'', IsMartingaleMeasure P ∧ HypLU μL μU P) ∧
      ∀ f : Ω T →ᵇ ℝ, InClaimFamilies f → Lam Ps μU f = supE P'' f := by sorry

end UncertainPricing.Superrep

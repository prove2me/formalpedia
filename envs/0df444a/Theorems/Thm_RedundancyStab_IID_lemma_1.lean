-- Prove2me | Theorems.Thm_RedundancyStab_IID_lemma_1
-- name    : RedundancyStab.IID.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:33.180222+00:00
-- url     : https://prove2.me/theorems/465d2101-32cb-42be-9cf0-bd4f20dbfbfb
-- title:
--   Lemma 1, pp. 6–7 — fluid limits exist (u.o.c. along a subsequence), are continuous, n_c = n_c(0) + λt/C(K,d) − µτ_c, τ_c nondecreasing, d-Lipschitz, τ_c ≤ d·t (corrected)
-- statement:
--   Consider the redundancy-$d$ model with i.i.d. $\mathrm{Exp}(\mu)$ copies under PS or under ROS, $1\le d\le K$, $\lambda>0$, $\mu>0$, with the fluid-scaled systems $N^{r}$ built from common primitives as in (2), and fix a fluid initial state $\vec n(0)\in\mathbb R_{\ge0}^{C}$. For almost every sample point $\omega$ and every sequence $r_k\to\infty$ of positive numbers there are a subsequence $r_{k_j}$ and functions $n_c,\tau_c$ ($c\in C$), continuous on $[0,\infty)$, such that for all $c\in C$
--   $$\lim_{j\to\infty}\frac{N^{r_{k_j}}_c(r_{k_j}t)}{r_{k_j}}=n_c(t)\quad\text{u.o.c.},\qquad \lim_{j\to\infty}\frac{T^{r_{k_j}}_c(r_{k_j}t)}{r_{k_j}}=\tau_c(t)\quad\text{u.o.c.},$$
--   and, for all $c\in C$ and $t\ge0$,
--   $$n_c(t)=n_c(0)+\frac{\lambda}{\binom{K}{d}}\,t-\mu\,\tau_c(t),$$
--   where $n_c(t)\ge0$, $\tau_c(0)=0$, $\tau_c(t)\le d\,t$, and $\tau_c$ is non-decreasing and Lipschitz continuous (with constant $d$) on $[0,\infty)$.
--
--   Lemma 1 provides the fluid limits whose drift Lemma 2 controls.
--
--   **Correction.** The paper prints $\tau_c(t)\le t$. That bound is false for $d\ge2$: with only type-$c$ jobs present, each of the $d$ servers of $c$ devotes its whole capacity to type $c$, so $T_c$ grows at rate $d$. Each $T_{s,c}$ grows at rate at most $1$, so the correct bound is $\tau_c(t)\le d\,t$, and the Lipschitz constant is $d$.
--
--   **Formalization Note** u.o.c. convergence is `TendstoUniformlyOn` on `Set.Icc 0 T` for every $T\ge0$ (`ConvergesUOC`). The order "for almost every $\omega$, for every sequence $r_k$" is kept. `pol` ranges over both disciplines.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, pp. 6–7, Lemma 1 (display (3) and the continuation on p. 7); bound τ_c(t) ≤ t corrected to τ_c(t) ≤ d·t

import Mathlib
import Definitions.Def_RedundancyStab_IID_FluidModel

namespace RedundancyStab.IID

open MeasureTheory ProbabilityTheory Filter

theorem lemma_1 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (hn0 : ∀ c, 0 ≤ n0 c) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ r : ℕ → ℝ, (∀ j, 0 < r j) → Tendsto r atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ n τ : JobType K d → ℝ → ℝ,
        ConvergesUOC P pol n0 ω (r ∘ φ) n τ ∧
        (∀ c, ContinuousOn (n c) (Set.Ici 0) ∧ ContinuousOn (τ c) (Set.Ici 0)) ∧
        (∀ c t, 0 ≤ t → n c t = n0 c + lam / (K.choose d : ℝ) * t - μ * τ c t) ∧
        (∀ c t, 0 ≤ t → 0 ≤ n c t) ∧
        (∀ c, τ c 0 = 0) ∧
        (∀ c t, 0 ≤ t → τ c t ≤ d * t) ∧
        (∀ c, MonotoneOn (τ c) (Set.Ici 0)) ∧
        (∀ c, LipschitzOnWith (d : NNReal) (τ c) (Set.Ici 0)) := by sorry

end RedundancyStab.IID

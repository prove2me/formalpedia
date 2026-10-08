-- Prove2me | Theorems.Thm_SmithHitAndRun_RandomDir_doob_case_b
-- name    : SmithHitAndRun.RandomDir.doob_case_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:49.998326+00:00
-- url     : https://prove2.me/theorems/10a2b32e-eef6-4ef8-8df1-123047a92608
-- title:
--   Doob's Case (b) bound $|P^m(A\mid x)-\pi(A)|\le(1-\delta\varphi(C))^{m-1}$ under a minorization on $C$
-- statement:
--   Let $P$ be a transition kernel on a measurable space $\alpha$, $\pi$ a probability measure with $\int P(A\mid x)\,\pi(\mathrm dx)=\pi(A)$ for all measurable $A$ (stationarity), $\varphi$ a finite measure and $C$ a measurable set with $\varphi(C)>0$. Assume
--
--   1. $P(\cdot\mid x)$ is a probability measure and $P(C^{\mathrm c}\mid x)=0$ for every $x\in C$, and $\pi(C^{\mathrm c})=0$;
--   2. for some $\delta>0$, $P(A\mid x)\ge\delta\,\varphi(A\cap C)$ for all $x\in C$ and all measurable $A$.
--
--   Then for every $x\in C$, every measurable $A$ and every $m\ge1$,
--   $$\bigl|P(X_m\in A\mid X_0=x)-\pi(A)\bigr|\le\bigl(1-\delta\,\varphi(C)\bigr)^{m-1}.$$
--
--   This is the geometric-ergodicity estimate the proof of Theorem 3 takes from Doob (1953), applied with $\varphi$ the $n$-dimensional content and $C=S$.
--
--   **Formalization Note** Doob's hypothesis is that the density $f(y\mid x)$ of the absolutely continuous part of $P(\cdot\mid x)$ with respect to $\varphi$ satisfies $f\ge\delta$ on $C\times C$; this implies the kernel-form minorization of item 2, which is used instead so that no Lebesgue decomposition has to be defined. In the paper the state space is $S$ and $C=S$ is all of it; here the state space is an arbitrary $\alpha$ and $C$ is a set the chain cannot leave and that carries $\pi$, which is what "$C=S$" means once the chain on $S$ is viewed inside $\mathbb R^n$. $P(X_m\in A\mid X_0=x)$ is the $m$-step kernel `MarkovChainCLT.iterKernel P m x A`.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1304, Proof of Theorem 3 (citing Doob 1953, p. 197, Case (b))

import Mathlib
import Definitions.Def_MarkovIterKernel

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.RandomDir

/-- Doob (1953), p. 197, Case (b), as used in the proof of Theorem 3 of Smith 1984 (p. 1304), with
the minorization written in kernel form. Let `P` be a transition kernel on `α`, `π` a stationary
probability measure, `φ` a finite measure and `C` a measurable set with `φ(C) > 0` that the chain
cannot leave and that carries `π`. If `P(A | x) ≥ δ φ(A ∩ C)` for all `x ∈ C` and measurable `A`
(which holds when the density of the absolutely continuous part of `P(· | x)` with respect to `φ`
is `≥ δ` on `C × C`), then for every `x ∈ C`, measurable `A` and `m ≥ 1`,
`|P(X_m ∈ A | X_0 = x) − π(A)| ≤ (1 − δ φ(C))^{m−1}`. -/
theorem doob_case_b {α : Type*} [MeasurableSpace α] (P : Kernel α α) (π φ : Measure α)
    [IsProbabilityMeasure π] [IsFiniteMeasure φ] (C : Set α) (hC : MeasurableSet C)
    (hφC : 0 < φ C) (hP : ∀ x ∈ C, IsProbabilityMeasure (P x))
    (hclosed : ∀ x ∈ C, P x Cᶜ = 0) (hπC : π Cᶜ = 0) (hinv : Kernel.Invariant P π)
    (δ : ℝ) (hδ : 0 < δ)
    (hmin : ∀ x ∈ C, ∀ A : Set α, MeasurableSet A → ENNReal.ofReal δ * φ (A ∩ C) ≤ P x A)
    (x : α) (hx : x ∈ C) (A : Set α) (hA : MeasurableSet A) (m : ℕ) (hm : 1 ≤ m) :
    |(MarkovChainCLT.iterKernel P m x A).toReal - (π A).toReal| ≤
      (1 - δ * (φ C).toReal) ^ (m - 1) := by sorry

end SmithHitAndRun.RandomDir

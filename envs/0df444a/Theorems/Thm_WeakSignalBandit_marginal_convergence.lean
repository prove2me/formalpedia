-- Prove2me | Theorems.Thm_WeakSignalBandit_marginal_convergence
-- name    : WeakSignalBandit.marginal_convergence
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:29:04.48815+00:00
-- url     : https://prove2.me/theorems/cc11d6e2-9407-4f32-8cff-c81fac7eabd5
-- title:
--   Proof of Theorem 1, p.35 — weak convergence of laws in $C$ implies $\mathbb E[f(Z^n_t)]\to\mathbb E[f(Z_t)]$ for every $t$ and bounded continuous $f$
-- statement:
--   Let $P_n$ and $P$ be probability laws on $\mathcal C=C([0,1],\mathbb R^d)$ such that $P_n$ converges weakly to $P$. Then for every $t\in[0,1]$ and every bounded continuous $f:\mathbb R^d\to\mathbb R$,
--   $$\lim_{n\to\infty}\int f(x(t))\,P_n(dx)=\int f(x(t))\,P(dx).$$
--
--   This is the closing step of the proof of Theorem 1, which turns weak convergence of the sample paths into the convergence (3.3) of expectations at each fixed time.
--
--   **Formalization Note** Weak convergence of laws on $\mathcal C$ is convergence of $\int F\,dP_n$ for every bounded continuous $F:\mathcal C\to\mathbb R$.
--
--   Differences from the source:
--   - generalization: the laws of the bandit's paths Z̄ⁿ in C([0,1], ℝ^{2K}) → any probability laws on C([0,1], ℝ^ι), ι finite; reason: the step uses only weak convergence of the laws; the bandit's laws are a special case
--   - reading: the convergence of E[f(Z̄ⁿ_1)] to E[f(Z_t)] → E[f(Z̄ⁿ_t)] → E[f(Z_t)] for every t ∈ [0,1]; reason: a misprint: the claim being proved is (3.3), for every t
--   - encoding: weak convergence in C → convergence of the integrals of every bounded continuous F : C → ℝ; reason: the definition of weak convergence of laws on C; the paths are measurable (checked in the verification file)
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, proof of Theorem 1 (closing paragraph), p.35

import Mathlib
import Definitions.Def_WeakSignalBandit_DiffusionLaw

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace WeakSignalBandit

/-- **Closing step of the proof of Theorem 1: weak convergence in `C` gives (3.3).** If laws `P_n`
on `C = C([0,1], ℝ^d)` converge weakly to `P`, then for every `t ∈ [0,1]` the marginal at time `t`
converges weakly: `E_{P_n}[f(Z_t)] → E_P[f(Z_t)]` for every bounded continuous `f : ℝ^d → ℝ`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, proof of Theorem 1, p.35 ("note that the weak convergence of `Z̄^n` in `C`
implies that the marginal distribution, `Z̄^n_t` converges weakly to `Z_t`").

**Formalization Note** Weak convergence of laws on `C` is convergence of `∫ F dP_n` for every
bounded continuous `F : C → ℝ`. The page's `E[f(Z̄^n_1)]` is read as `E[f(Z̄^n_t)]` for every
`t`, as in (3.3). -/
theorem marginal_convergence {ι : Type*} [Fintype ι]
    (Pn : ℕ → Measure (Path ι)) [∀ n, IsProbabilityMeasure (Pn n)]
    (P : Measure (Path ι)) [IsProbabilityMeasure P]
    (hconv : ∀ F : Path ι →ᵇ ℝ, Tendsto (fun n => ∫ x, F x ∂(Pn n)) atTop (𝓝 (∫ x, F x ∂P)))
    (t : unitInterval) (f : Sp ι →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f (x t) ∂(Pn n)) atTop (𝓝 (∫ x, f (x t) ∂P)) := by sorry

end WeakSignalBandit

-- Prove2me | Theorems.Thm_WeakSignalBandit_transition_kernel_A14
-- name    : WeakSignalBandit.transition_kernel_A14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:46.002311+00:00
-- url     : https://prove2.me/theorems/46780823-953f-4caf-8056-a247a7e21d6d
-- title:
--   (A.14), p.33 — the scaled state of the $n$-th experiment is a Markov chain with transition kernel $\Pi^n((q,s),(q+e_k/n,s+e_k\,ds/\sqrt n))=\bar\psi^n_k(q,s)P^n_k(ds)$
-- statement:
--   Fix $n\ge1$, reward distributions $P^n_1,\dots,P^n_K$ and a sampling function $\psi^n$ (measurable, with values in the simplex $\Delta^K$). In any realization of the $n$-th sequentially randomized Markov experiment, the scaled state $Z^n_i=(Q^n_i,S^n_i)$ of (2.10) satisfies, for every period $i<n$ and every Borel set $B\subseteq\mathbb R^{2K}$,
--   $$\mathbb P\big(Z^n_{i+1}\in B\ \big|\ A_1,Y_1,\dots,A_i,Y_i\big)=\Pi^n(Z^n_i,B)\quad\text{almost surely},$$
--   where $\Pi^n$ is the kernel (A.14):
--   $$\Pi^n\big((q,s),(q+e_k/n,\ s+e_k\,ds/\sqrt n)\big)=\bar\psi^n_k(q,s)\,P^n_k(ds),\qquad k=1,\dots,K,$$
--   and zero elsewhere.
--
--   This is the statement that the pre-limit process is a time-homogeneous Markov chain with kernel $\Pi^n$, which is what Theorem 11 requires.
--
--   **Formalization Note** Lean period $i$ is the paper's period $i+1$. The conditioning is on the full observed history of the first $i$ periods, which contains $\sigma(Z^n_0,\dots,Z^n_i)$.
--
--   Differences from the source:
--   - generalization: the transition kernel of the pre-limit chain Z̄ⁿ, P(Zⁿ_{i+1} ∈ A | Zⁿ_i = z) (A.4) → the conditional law of Zⁿ_{i+1} given the whole observed history A_1, Y_1, …, A_i, Y_i is Πⁿ(Zⁿ_i, ·); reason: the history contains σ(Zⁿ_0, …, Zⁿ_i), so by the tower property this implies the Markov property (A.4)
--   - encoding: n unrestricted, periods i = 1, …, n → 0 < n and Lean periods i < n; reason: the scaling 1/n, 1/√n needs n ≥ 1; the experiment of Definition 1 has horizon n
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.14) p.33

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment
import Definitions.Def_WeakSignalBandit_BanditKernel

open MeasureTheory Filter

namespace WeakSignalBandit

/-- **(A.14): the transition kernel of the scaled state.** In the `n`-th experiment (a stochastic
`K`-armed bandit with reward distributions `P^n_k` run by a sequentially randomized Markov
experiment with sampling function `ψ^n`), the scaled state `Z^n_i = (Q^n_i, S^n_i)` of (2.10)
moves according to `Π^n`: for every period `i < n` and every Borel set `B ⊆ ℝ^{2K}`,
`ℙ(Z^n_{i+1} ∈ B | A_1, Y_1, …, A_i, Y_i) = Π^n(Z^n_i, B)` almost surely, where
`Π^n((q, s), (q + e_k/n, s + e_k ds/√n)) = ψ̄^n_k(q, s) P^n_k(ds)`, `k = 1, …, K`, and zero
elsewhere.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.14) p.33 ("The transition kernel of the pre-limit chain `Z̄^n` can be
written as").

**Formalization Note** Lean period `i` is the paper's period `i + 1`; `Z^n_i` is
`scaledState n A Y i`. The conditioning is on the observed history of the first `i` periods, which
contains `σ(Z^n_0, …, Z^n_i)`. `n ≥ 1` (the scaling `1/n`, `1/√n` needs it). -/
theorem transition_kernel_A14 {K : ℕ} (n : ℕ) (hn : 0 < n)
    (P : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (P k)]
    (ψ : State K → Fin K → ℝ) (hψ : IsSamplingFunction ψ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (hexp : IsSRMExperiment n Pr P ψ A Y)
    (i : ℕ) (hi : i < n) (B : Set (State K)) (hB : MeasurableSet B) :
    condExp (history A Y i) Pr
        (((fun ω => scaledState n A Y (i + 1) ω) ⁻¹' B).indicator fun _ => (1 : ℝ)) =ᵐ[Pr]
      fun ω => (banditKernel n P ψ (scaledState n A Y i ω) B).toReal := by sorry

end WeakSignalBandit

-- Prove2me | Theorems.Thm_WeakSignalBandit_theorem_1
-- name    : WeakSignalBandit.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:15.517248+00:00
-- url     : https://prove2.me/theorems/71dffca3-8b83-4ffc-9e59-385e1b48af47
-- title:
--   Theorem 1, pp.12–13 — sample paths of Lipschitz sequentially randomized Markov experiments converge weakly in $C$ to the unique solution of (3.1) (corrected: uniqueness in law assumed)
-- statement:
--   Fix $K\in\mathbb N$, $\mu\in\mathbb R^K$ and $\sigma\in\mathbb R^K_+$. For each $n$, consider a $K$-armed bandit with horizon $n$ (Definition 1) whose reward distributions $\{P^n_k\}$ reside in the weak signal regime with parameters $\mu,\sigma$ (Definition 3),
--   $$\lim_{n\to\infty}\sqrt n\,\mu^n_k=\mu_k,\qquad\lim_{n\to\infty}(\sigma^n_k)^2=\sigma_k^2,$$
--   and admit fourth moments that are uniformly bounded across $k$ and $n$. Suppose the $n$-th problem is run by a sequentially randomized Markov experiment with measurable sampling function $\psi^n:\mathbb R^K\times\mathbb R^K\to\Delta^K$ (Definition 2), that the sequence $\psi^n$ is convergent with limit $\psi$ (Definition 4), and that $\psi$ is Lipschitz-continuous on $D=[0,1]^K\times\mathbb R^K$. Let $(\bar Q^n_t,\bar S^n_t)_{t\in[0,1]}$ be the interpolated scaled sample path (3.2) of any realization of the $n$-th experiment; $(\bar Q^n_0,\bar S^n_0)=0$. Suppose further that any two solution laws of (3.1) below, on $\mathcal C$ and from $0$, coincide.
--
--   Then there is a unique law $P$ on $\mathcal C=C([0,1],\mathbb R^{2K})$ of a solution $(Q_t,S_t)_{t\in[0,1]}$ of
--   $$dQ_{k,t}=\psi_k(Q_t,S_t)\,dt,\qquad dS_{k,t}=\mu_k\psi_k(Q_t,S_t)\,dt+\sigma_k\sqrt{\psi_k(Q_t,S_t)}\,dB_{k,t},\qquad (Q_0,S_0)=0,\tag{3.1}$$
--   with $B$ a standard Brownian motion in $\mathbb R^K$ with independent components; as $n\to\infty$, $(\bar Q^n,\bar S^n)$ converges weakly in $\mathcal C$ to $P$; and
--   $$\lim_{n\to\infty}\mathbb E\big[f(\bar Q^n_t,\bar S^n_t)\big]=\mathbb E\big[f(Q_t,S_t)\big]\qquad\text{for all }t\in[0,1]\tag{3.3}$$
--   and every bounded continuous $f:\mathbb R^{2K}\to\mathbb R$.
--
--   This is the paper's first main result: a broad class of adaptive experiments (tempered greedy, Luce's rule, Thompson sampling with a Lipschitz limit) has a diffusion limit, which is then used to analyse the regret of these experiments in the weak signal regime.
--
--   **Formalization Note** Solutions of (3.1) are represented by their laws through the martingale problem on $[0,1]$ with the coefficients $b=(\psi_k,\psi_k\mu_k)$ and $a=\mathrm{diag}_{I_S}(\psi_k\sigma_k^2)$. Arms are `Fin K` and Lean period $i$ is the paper's period $i+1$. Each experiment is any probability space carrying actions and rewards with the conditional laws of Definitions 1–2 for periods $1,\dots,n$.
--
--   Differences from the source:
--   - correction: ψ Lipschitz alone is claimed to give a unique solution of (3.1) and convergence to it → added hypothesis huniq: any two solution laws of (3.1) from 0 coincide; reason: the printed statement is false. Counterexample with K = 2, μ = 0, σ = (1, 1), ψ_1(q, s) = min(1, |q_1| + |s_1|), ψ_2 = 1 − ψ_1, rewards ±1 with probability ½, ψⁿ(Q, S) = ψ(Q/n, S/√n): two laws solve (3.1) from 0, namely (a) Q_1 ≡ S_1 ≡ 0, Q_{2,t} = t, S_2 = B_2, and (b) Q_1 = X, S_1 = W∘X, Q_{2,t} = t − X_t, S_{2,t} = ∫_0^t √(1 − X′_u) dB_{2,u}, with X the inverse of τ(x) = ∫_0^x du/ψ_1(u, W_u), which is a.s. finite. σ_k√ψ_k is not Lipschitz where ψ_k vanishes, while the cited Karatzas–Shreve Thm 5.2.9 needs Lipschitz dispersion. The theorem's own conclusion implies huniq, so it is the minimal repair; huniq holds for instance when every √ψ_k is Lipschitz on D
--   - encoding: solution of the SDE driven by a Brownian motion → solution law of the martingale problem on [0,1] tested with all smooth compactly supported f and finite products of bounded measurable functions of past values (IsDiffusionLaw); reason: Mathlib has no Itô integral; a law solves the martingale problem for (a, b) exactly when it is the law of a weak solution of the SDE with ηηᵀ = a (Ethier–Kurtz Ch. 5, Prop. 3.1, Thm 3.3)
--   - reading: converges weakly to the unique solution → a solution law L exists, every solution law equals L, and the laws converge weakly to L; reason: weak convergence identifies only the law; footnote 5 (p.32) says the SDE is determined by a up to the choice of η, i.e. uniqueness is in law
--   - encoding: weak convergence in C → convergence of the integrals of every bounded continuous F : C → ℝ; reason: the definition of weak convergence of laws on C; the paths are measurable (checked in the verification file)
--   - reading: Definition 3: μ, σ ∈ ℝ^K_+ → μ ∈ ℝ^K arbitrary, σ_k ≥ 0; reason: Theorem 1 itself fixes μ ∈ ℝ^K and σ ∈ ℝ^K_+; the paper's examples (centered Bernoulli rewards, p.10; §4) have negative μ_k
--   - reading: Definition 1: A_i is measurable with respect to the observed history; Definition 2: A_i | history ∼ Multinomial(π_i) → the two conditional laws P(A_i = k | history) = ψ_k(Q_{i−1}, S_{i−1}) and P(Y_i ∈ B | history, A_i) = P_{A_i}(B), for the periods 1, …, n, on any probability space; reason: Definition 1's measurability cannot be literal for a randomized draw; the two conditional laws are the content of Definitions 1–2 and determine the joint law
--   - encoding: ψ : [0,1]^K × ℝ^K → Δ^K Lipschitz, the limit of ψ̄ⁿ on compact subsets of [0,1]^K × ℝ^K → ψ a function on ℝ^{2K}, constrained only on D = [0,1]^K × ℝ^K (convergence on compact subsets of D, LipschitzOnWith on D); the coefficients of (3.1) read ψ at the projection onto D; reason: the values of ψ off D are not given by the source and never enter: a solution from 0 has Q_t ∈ [0,1]^K for t ≤ 1
--   - encoding: arms 1, …, K; periods i = 1, …, n; state space ℝ^K × ℝ^K → Fin K; Lean periods 0, …, n − 1; EuclideanSpace ℝ (Fin K ⊕ Fin K); reason: Lean conventions; same instances
--   - encoding: hypothesis (Q̄ⁿ_0, S̄ⁿ_0) = 0 → not a hypothesis; reason: it holds by construction from the convention Q_{k,0} = S_{k,0} = 0 (p.7)
--   - encoding: A_i, Y_i for the periods 1, …, n → sequences A_i, Y_i indexed by all i ∈ ℕ, all measurable, constrained only for the periods 1, …, n; reason: the values after period n enter the interpolation (3.2) only with weight 0 at t = 1
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, Theorem 1, pp.12–13; Definitions 1–4, pp.7–10; (3.1)–(3.3), pp.12–13; (A.1)–(A.3), (A.15)–(A.17), pp.31, 33

import Mathlib
import Definitions.Def_WeakSignalBandit_DiffusionLaw
import Definitions.Def_WeakSignalBandit_Experiment
import Definitions.Def_WeakSignalBandit_LimitCoefficients

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace WeakSignalBandit

/-- **Theorem 1 (diffusion limit of Lipschitz sequentially randomized Markov experiments;
corrected: uniqueness in law of (3.1) is assumed).** Fix
`K ∈ ℕ`, `μ ∈ ℝ^K` and `σ ∈ ℝ^K_+`. Suppose that the `n`-th problem is a `K`-armed bandit
(Definition 1) whose reward distributions `{P^n_k}` reside in the weak signal regime (Definition 3)
with parameters `μ, σ` and admit fourth moments uniformly bounded across `k` and `n`, run by a
sequentially randomized Markov experiment with sampling function `ψ^n` (Definition 2), where the
sequence `ψ^n` is convergent with limit `ψ` (Definition 4), `ψ` is Lipschitz-continuous, and
(3.1) is unique in law from `0`. Then, as `n → ∞`, the interpolated scaled sample paths `(Q̄^n_t, S̄^n_t)_{t∈[0,1]}` (3.2) converge weakly
in `C = C([0,1], ℝ^{2K})` to `(Q_t, S_t)_{t∈[0,1]}`, the unique solution over `t ∈ [0,1]` of
`dQ_{k,t} = ψ_k(Q_t, S_t) dt`, `dS_{k,t} = μ_k ψ_k(Q_t, S_t) dt + σ_k √ψ_k(Q_t, S_t) dB_{k,t}` (3.1)
with `(Q_0, S_0) = 0` and `B` a standard Brownian motion in `ℝ^K` with independent components.
Furthermore, `lim_{n→∞} E[f(Q̄^n_t, S̄^n_t)] = E[f(Q_t, S_t)]` for all `t ∈ [0,1]` and every bounded
continuous `f : ℝ^{2K} → ℝ` (3.3).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, Theorem 1, pp.12–13; Definitions 1–4 pp.7–10; (3.1)–(3.3) p.12–13.

**Formalization Note**
1. The SDE (3.1) is encoded by its martingale problem on `[0,1]` (`IsDiffusionLaw`) with
   coefficients `limitDrift μ ψ` and `limitDiff σ ψ` ((A.15), (A.17)), started at `0`; "the unique
   solution" is uniqueness in law: a solution law `L` exists and every solution law equals `L`.
2. The `n`-th experiment is any probability space `(Ω n, Pr n)` with actions `A n` and rewards
   `Y n` satisfying the conditional laws of Definitions 1–2 for the periods `1, …, n`
   (`IsSRMExperiment`); `ψn n` is `ψ^n`, a measurable `Δ^K`-valued function on `ℝ^K × ℝ^K`.
3. Arms are `Fin K`; Lean period `i` is the paper's period `i + 1`; the state space is
   `ℝ^{2K}` with coordinates `Sum.inl k` (`q_k`) and `Sum.inr k` (`s_k`) and the Euclidean norm.
4. `ψ` is only constrained on `D = [0,1]^K × ℝ^K` (Definition 4): convergence on compact subsets
   of `D` and Lipschitz on `D`; the coefficients read `ψ` through the projection onto `D`.
5. Weak convergence in `C` is convergence of `∫ F(Q̄^n, S̄^n) dPr n` for every bounded continuous
   `F : C → ℝ`. `(Q̄^n_0, S̄^n_0) = 0` holds by construction (`Q_{k,0} = S_{k,0} = 0`).

**Correction** The page has no hypothesis `huniq`, and the theorem is false without it: `σ_k √ψ_k`
need not be Lipschitz where `ψ_k` vanishes, while the page's proof relies on Theorem 11 and
Karatzas–Shreve Thm 5.2.9. Counterexample: `K = 2`, `μ = 0`, `σ = (1, 1)`,
`ψ_1(q, s) = min(1, |q_1| + |s_1|)`, `ψ_2 = 1 − ψ_1`, rewards `±1` with probability `½`,
`ψ^n(Q, S) = ψ(Q/n, S/√n)`. Two laws solve (3.1) from `0`:
(a) `Q_1 ≡ S_1 ≡ 0`, `Q_{2,t} = t`, `S_2 = B_2`;
(b) `Q_1 = X`, `S_1 = W ∘ X`, `Q_{2,t} = t − X_t`, `S_{2,t} = ∫_0^t √(1 − X'_u) dB_{2,u}`, where `W`
and `B_2` are independent Brownian motions and `X` is the inverse of
`τ(x) = ∫_0^x du / ψ_1(u, W_u)`, which is a.s. finite because
`E[1/(u + |W_u|)] ≤ C u^{-1/2}(1 + |log u|)` near `0`; thus `X' = ψ_1(X, W ∘ X)`, `X_t > 0` for
`t > 0`, each `X_t` is a stopping time of `W`, and `W ∘ X` is a martingale with bracket `X`.
Uniqueness therefore fails, and the convergence fails with it: the chain above stays in law (a)
(arm 1 is never pulled), while `ψ^n_1 = ψ_1 + ε_n`, suitably renormalized with `ε_n → 0` slowly,
tends to (b). -/
theorem theorem_1 {K : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (P : ℕ → Fin K → Measure ℝ) [∀ n k, IsProbabilityMeasure (P n k)]
    (hweak : IsWeakSignal P μ σ) (h4 : HasBoundedFourthMoments P)
    (ψn : ℕ → State K → Fin K → ℝ) (hψn : ∀ n, IsSamplingFunction (ψn n))
    (ψ : State K → Fin K → ℝ) (hconv : IsConvergentSampling ψn ψ)
    (hLip : ∃ L, LipschitzOnWith L ψ domainD)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Pr : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Pr n)]
    (A : ∀ n, ℕ → Ω n → Fin K) (Y : ∀ n, ℕ → Ω n → ℝ)
    (hexp : ∀ n, IsSRMExperiment n (Pr n) (P n) (ψn n) (A n) (Y n))
    (huniq : ∀ L L' : Measure (Path (Fin K ⊕ Fin K)),
      IsDiffusionLaw (limitDiff σ ψ) (limitDrift μ ψ) 0 L →
      IsDiffusionLaw (limitDiff σ ψ) (limitDrift μ ψ) 0 L' → L = L') :
    ∃ L : Measure (Path (Fin K ⊕ Fin K)),
      IsDiffusionLaw (limitDiff σ ψ) (limitDrift μ ψ) 0 L ∧
      (∀ L' : Measure (Path (Fin K ⊕ Fin K)),
        IsDiffusionLaw (limitDiff σ ψ) (limitDrift μ ψ) 0 L' → L' = L) ∧
      (∀ F : Path (Fin K ⊕ Fin K) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (banditPath n (A n) (Y n) ω) ∂(Pr n)) atTop
          (𝓝 (∫ x, F x ∂L))) ∧
      ∀ (t : unitInterval) (f : State K →ᵇ ℝ),
        Tendsto (fun n => ∫ ω, f (banditPath n (A n) (Y n) ω t) ∂(Pr n)) atTop
          (𝓝 (∫ x, f (x t) ∂L)) := by sorry

end WeakSignalBandit

-- Prove2me | Theorems.Thm_WeakSignalBandit_fourth_moment_A18
-- name    : WeakSignalBandit.fourth_moment_A18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:16.563989+00:00
-- url     : https://prove2.me/theorems/769a7b04-4916-4624-99a1-ec288e183dca
-- title:
--   (A.18), p.33 — $m^n_4(z)=\int|z'-z|^4K^n(z,dz')\to0$ uniformly over all $z$
-- statement:
--   Let $P^n_k$ be probability distributions on $\mathbb R$ whose fourth moments are uniformly bounded, $\sup_{n,k}\mathbb E_{P^n_k}[Y^4]<\infty$, and let $\psi^n$ be functions with values in the unit simplex $\Delta^K$. Let $\Pi^n$ be the kernel (A.14) and $K^n=n\Pi^n$. Then
--   $$\sup_{z\in\mathbb R^{2K}}m^n_4(z)=\sup_{z}\int|z'-z|^4\,K^n(z,dz')\ \xrightarrow{n\to\infty}\ 0,$$
--   uniformly over all $z\in\mathbb R^{2K}$.
--
--   This is the moment condition (A.11) of Lemma 12 for $p=4$ in the bandit model, on the whole state space.
--
--   **Formalization Note** $|\cdot|$ is the Euclidean norm, so a jump of arm $k$ with reward $w$ has $|z'-z|^2=1/n^2+w^2/n$. Uniform convergence of the $[0,\infty]$-valued $m^n_4$ is written as: for every $\epsilon>0$, eventually $m^n_4(z)\le\epsilon$ for all $z$.
--
--   Differences from the source:
--   - generalization: ψⁿ the sampling functions of a convergent sequence of experiments, rewards in the weak signal regime → ψⁿ any functions with values in Δ^K; no weak-signal hypothesis; reason: the computation uses only 0 ≤ ψ̄ⁿ_k, Σ_k ψ̄ⁿ_k = 1 and the fourth-moment bound; the source's setting satisfies these
--   - reading: as n → 0 → as n → ∞; reason: a misprint: the display itself is a limit as n → ∞
--   - encoding: sup_z m^n_4(z) → 0 → for every ε > 0, eventually m^n_4(z) ≤ ε for all z, with m^n_4 valued in [0, ∞]; reason: the same statement for a [0, ∞]-valued moment
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.18) p.33

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment
import Definitions.Def_WeakSignalBandit_ChainCharacteristics
import Definitions.Def_WeakSignalBandit_BanditKernel

open MeasureTheory Filter

namespace WeakSignalBandit

/-- **(A.18): the fourth moments of `K^n` vanish uniformly.** Let `P^n_k` be reward distributions
whose fourth moments are uniformly bounded across `k` and `n`, let `ψ^n` be sampling functions with
values in the simplex `Δ^K`, and let `K^n = nΠ^n` with `Π^n` the kernel (A.14). Then
`m^n_4(z) = ∫ |z′ − z|^4 K^n(z, dz′) → 0` as `n → ∞`, uniformly over all `z ∈ ℝ^{2K}`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.18) p.33 ("as n → 0, uniformly over all z").

**Formalization Note** `|·|` is the Euclidean norm on `ℝ^{2K}`, so `|z′ − z|² = 1/n² + w²/n` for a
jump of arm `k` with reward `w`. Uniform convergence of the `[0, ∞]`-valued `m^n_4` is written as
"for every `ε > 0`, eventually `m^n_4(z) ≤ ε` for all `z`". -/
theorem fourth_moment_A18 {K : ℕ} (P : ℕ → Fin K → Measure ℝ)
    [∀ n k, IsProbabilityMeasure (P n k)] (h4 : HasBoundedFourthMoments P)
    (ψn : ℕ → State K → Fin K → ℝ) (hψn : ∀ n z, ψn n z ∈ stdSimplex ℝ (Fin K)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z : State K,
      momentP (scaledKernel (banditKernel n (P n) (ψn n)) n) 4 z ≤ ENNReal.ofReal ε := by sorry

end WeakSignalBandit

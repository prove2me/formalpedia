-- Prove2me | Theorems.Thm_QubitFreqSensing_section_7_outcome
-- name    : QubitFreqSensing.section_7_outcome
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:51.90488+00:00
-- url     : https://prove2.me/theorems/21b56976-a946-4cbf-8a00-cc17f1b7b4aa
-- title:
--   §7 — the $Y$-pulse block implements the sign pattern: outcome $1$ has probability $\sin^2\!\int_0^T f(t)h(a+\tau+t)\,dt$
-- statement:
--   Consider a pulse block with durations $d_1,\dots,d_m\ge0$, breakpoints $t_k=d_1+\dots+d_k$ ($t_0=0$, $t_m=T$), a sign $\sigma_1\in\{1,-1\}$, start gate $G_0=e^{i\sigma_1\pi Y/4}$, a pulse $Y$ between consecutive pieces, and finish gate $(G_{m-1}\cdots G_0)^\dagger=e^{-i\sigma_1\pi Y/4}Y^{m-1}$, as in Protocol 1. Let $f=\sigma_k=\sigma_1(-1)^{k-1}$ on the $k$-th piece $[t_{k-1},t_k)$. For every field $h$, every start time $a$ and every wait $\tau$, the trial run under $h(t)Z$ gives outcome $1$ with probability
--
--   $$
--   p_1(h,a,\tau)=\sin^2\Bigl(\int_0^T f(t)\,h(a+\tau+t)\,dt\Bigr).
--   $$
--
--   For $h\equiv0$ this is $0$: the protocol has no false positives. For $h(t)=B\cos(\omega t+\phi)$ it is $\sin^2 A_{\omega,\phi+\omega a,T,\tau}(f)$, the probability (9) with the phase advanced to the trial's start time.
--
--   **Formalization Note** The integral is written piece by piece as $\sum_{k}\sigma_1(-1)^k\int_{a+\tau+t_k}^{a+\tau+t_{k+1}}h$ with $0$-based $k$.
--
--   Differences from the source:
--   - generalization: the signal field B cos(ω(t + τ) + ϕ) → every field h : ℝ → ℝ; reason: the computation C_k†ZC_k = σ_kX never uses the form of the field; h = B cos(ω· + ϕ) and h = 0 are special cases
--   - encoding: the outcome distribution of measuring |c(T)⟩ = exp(−iBX∫_0^T f(t)cos(ω(t+τ)+ϕ)dt)|0⟩ → the probability pOne of outcome 1 equals sin² of the integral; reason: a single-qubit outcome distribution is determined by the probability of 1
--   - encoding: ∫_0^T f(t)(…)dt with f = σ_k on [t_{k−1}, t_k) → Σ_k σ₁(−1)^k ∫ over the k-th piece, 0-based; reason: the same integral
--   - generalization: 0 = t0 < t1 < ⋯ < tm = T with empty pieces discarded and equal neighbours merged → any durations d_1, …, d_m ≥ 0 (empty pieces allowed), the sign alternating from piece to piece; reason: the identity C_k†ZC_k = σ_kX holds piece by piece whatever the lengths; the merged pattern of Protocol 1 is a special case
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §7, pp.25–26, eqs. (19)–(21), with eq. (9), p.15 (PDF pp.25–26)

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_QubitFreqSensing_Propagator
import Definitions.Def_QubitFreqSensing_PulseProtocol

open Real

namespace QubitFreqSensing

/-- **§7: the pulses implement the sign pattern** (Chen, Coladangelo, Li, Zhang, manuscript (STOC
2027 submission), §7, pp.25–26, with eqs. (9), (19)–(21)). "Since the final operation in our
protocol (before the final measurement) is to apply C†m, the final state is C†m |ψ(T)⟩ =
C†mCm |c(T)⟩ = |c(T)⟩. So, the outcome distribution of our protocol is that of measuring |c(T)⟩ in
the standard basis", where `|c(T)⟩ = exp(−iBX ∫₀^T f(t) cos(ω(t+τ)+ϕ) dt)|0⟩`.

Let a block have durations `d₁, …, d_m` (pieces `[t_{k−1}, t_k)`, `t_k = d₁ + ⋯ + d_k`), signs
`σ_k = σ₁(−1)^{k−1}`, start gate `G₀ = e^{iσ₁πY/4}` and finish gate `(G_{m−1}⋯G₀)† =
e^{−iσ₁πY/4}Y^{m−1}` (Protocol 1, p.12). For a trial starting at absolute time `a` with wait `τ`,
under any field `h`, the probability of outcome `1` is `sin²(∫₀^T f(t) h(a + τ + t) dt)`, `f = σ_k`
on the `k`-th piece; for `h = B cos(ω·+ϕ)` this is `sin²(A_{ω, ϕ+ωa, T, τ}(f))` (eq. (9)), and for
`h ≡ 0` it is `0`.

**Formalization Note** The integral `∫₀^T f(t) h(a+τ+t) dt` is written piece by piece,
`Σ_k σ₁(−1)^k ∫_{a+τ+t_k}^{a+τ+t_{k+1}} h` (0-based `k`, `t_k` the partial sums). The identity holds
for every field `h`, not only `B cos(ω t + ϕ)`. -/
theorem section_7_outcome (σ₁ : ℝ) (hσ : σ₁ = 1 ∨ σ₁ = -1) (blk : PulseBlock)
    (hstart : blk.start.1 = expIY (σ₁ * π / 4))
    (hfinish : blk.finish.1 =
      expIY (-(σ₁ * π / 4)) * MIPRE.LCS.Pauli.Y ^ (blk.durations.length - 1))
    (h : ℝ → ℝ) (a τ : ℝ) :
    pOne h a τ blk = Real.sin (∑ k : Fin blk.durations.length,
      σ₁ * (-1) ^ (k : ℕ) * ∫ t in (a + τ + (blk.durations.take k).sum)..
        (a + τ + (blk.durations.take (k + 1)).sum), h t) ^ 2 := by sorry

end QubitFreqSensing

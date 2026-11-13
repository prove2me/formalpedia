-- Prove2me | Theorems.Thm_SigRoute_lemma_11_gating
-- name    : SigRoute.lemma_11_gating
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:41:47.107197+00:00
-- url     : https://prove2.me/theorems/7729818f-534e-49c5-90d5-b2922236828d
-- title:
--   Lemma 11, first sentence — gating: $w_1>1-\theta$ and $\rho(\nu)=A$ imply $\sigma_1(\nu)=1$
-- statement:
--   Let $(\sigma,w,\theta)$ be a signal system whose correctness signal is $\sigma_1(\nu)=1[V_0\text{ accepts in }\nu]$. If the correctness signal has weight
--
--   $$
--   w_1>1-\theta,
--   $$
--
--   then for every view $\nu$, $\rho(\nu)=A$ implies $\sigma_1(\nu)=1$.
--
--   Thus with gating, a round reaches arm $A$ only when the base verifier accepted.
--
--   Differences from the source:
--   - generalization: efficiently computable signals $\sigma_i:\{0,1\}^*\to[0,1]$ → maps $\sigma_i:W\to[0,1]$ on an arbitrary type $W$ of views; reason: the paper uses only that each $\sigma_i$ maps into $[0,1]$ (p.5); bit-string views are an instance
--   - encoding: signals $\sigma_1,\dots,\sigma_k$ with weights $w_1,\dots,w_k$, correctness signal $\sigma_1$ with $\sigma_1(\nu)=1[V_0\text{ accepts in }\nu]$ → signals indexed by `Fin (k+1)`, index `0` the correctness signal, with $\sigma_1=\mathbf 1_{\mathrm{acc}_0}$ for the set $\mathrm{acc}_0$ of accepting views (`IsCorrectnessSignal`); reason: relabelling of the printed convention; $V_0$'s acceptance is the set $\mathrm{acc}_0$
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 11, first sentence, p.7

import Mathlib
import Definitions.Def_SigRoute_SignalSystem

namespace SigRoute

/-- Lemma 11 (Gating), first sentence (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 11, p.7): if the correctness signal has weight
`w_1 > 1 − θ`, then `ρ(ν) = A` implies `σ_1(ν) = 1`.

**Formalization Note** Index `0` is the paper's correctness signal `σ_1` with weight `w_1`; the paper's
convention `σ_1(ν) = 1[V_0 accepts in ν]` (p.5) is the hypothesis `IsCorrectnessSignal S acc₀`, with
`acc₀` the set of views in which the base verifier accepts. -/
theorem lemma_11_gating {W : Type*} {k : ℕ} (S : SignalSystem W k) (acc₀ : Set W)
    (hσ₁ : S.IsCorrectnessSignal acc₀) (hgate : 1 - S.θ < S.w 0) (ν : W) :
    S.route ν = Arm.A → S.sig ν 0 = 1 := by sorry

end SigRoute

-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_3_2
-- name    : ParityBarrier563.Trilinear.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:03.990012+00:00
-- url     : https://prove2.me/theorems/a5e698bd-1a45-490f-91c1-1b525e410564
-- title:
--   Lemma 3.2 — small b-CNF correlation after two restrictions gives E_φ corr_k(ψ_φ) ≤ ε + δ (with ε ≥ 0)
-- statement:
--   Let $k\ge b\ge1$ be integers, let $p=b/(64k)$, and let $\psi:\{0,1\}^V\to[-1,1]$. Let $\varphi$ be a random restriction of $V$ with an arbitrary distribution, and, given $\varphi$, let $\rho$ be a $p$-random restriction of $\mathrm{live}(\varphi)$. Let $\varepsilon\ge0$ and $\delta$ be numbers such that
--
--   $$\Pr_{\varphi,\rho}\bigl[\mathrm{corr}_b(\psi_{\varphi\rho})>\varepsilon\bigr]\le\delta .$$
--
--   Then
--
--   $$\mathbb E_\varphi\,\mathrm{corr}_k(\psi_\varphi)\le\varepsilon+\delta .$$
--
--   Combined with Lemma 3.1 this is the transfer from narrow to wide CNF tests used in Lemma 5.5.
--
--   Differences from the source:
--   - reading: ε unconstrained → ε ≥ 0; reason: the printed statement is false for ε < 0: take ψ ≡ 1, φ all live with probability one, ε = −1/2, δ = 1; the hypothesis holds since every probability is at most 1, while corr_k(ψ) = 1 > 1/2 = ε + δ; the source uses ε = 2^{−m/32} > 0
--   - encoding: φ with any distribution → nonnegative weights on the finite set of restrictions of V summing to one; ψ_{φρ} is the iterated restriction (ψ_φ)_ρ; reason: every law on a finite set is such a weight function
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 3.2, printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 3.2, printed p.13 / PDF 15. The first restriction `φ` has an arbitrary law `w`
(nonnegative weights summing to one on the finite set of restrictions of `V`); given `φ`, `ρ` is a
`p`-random restriction of `live(φ)` with `p = b/(64k)`. -/
theorem lemma_3_2 (V : Type) [Fintype V] [DecidableEq V] (k b : ℕ) (ψ : RealFn V)
    (w : Restriction V → ℝ) (ε δ : ℝ)
    (hb : 1 ≤ b) (hbk : b ≤ k) (hψ : ∀ x, ψ x ∈ Set.Icc (-1 : ℝ) 1)
    (hw0 : ∀ φ, 0 ≤ w φ) (hw1 : ∑ φ, w φ = 1) (hε : 0 ≤ ε)
    (hfail : ∑ φ, w φ * restrProb ((b : ℝ) / (64 * k))
        (fun ρ : Restriction (Live φ) => ¬ corr b (restrict ρ (restrict φ ψ)) ≤ ε) ≤ δ) :
    ∑ φ, w φ * corr k (restrict φ ψ) ≤ ε + δ := by sorry

end ParityBarrier563.Trilinear

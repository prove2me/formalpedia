-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_13
-- name    : PQNormIPM1352.Main.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:22.36044+00:00
-- url     : https://prove2.me/theorems/24c82325-0819-4f86-a8e0-e8542ede00a2
-- title:
--   Lemma 13 — inexact Newton step (corrected: $F$ closed, and $x^+\in\mathrm{int}(K)$ concluded)
-- statement:
--   Let $K \subseteq \mathbb R^N$ be closed and convex with nonempty interior and let $F$ be self-concordant on $\mathrm{int}(K)$ and diverge at the boundary of $K$ (a closed self-concordant function in the sense of [NN94]), with invertible Hessian on $\mathrm{int}(K)$. Let $x\in\mathrm{int}(K)$ with Newton decrement $\lambda(x) = \lambda < 1$, and let $\tilde\Delta$ satisfy $\|\tilde\Delta - \Delta(x)\|_x \le \delta\|\Delta(x)\|_x$ for some $\delta < \min\{1/2, (1-\lambda)/\lambda\}$. Then $x^+ = x + \tilde\Delta$ lies in $\mathrm{int}(K)$ and
--   $$\lambda(x^+) \le \frac{\delta\lambda + (1+\delta)\lambda^2}{\big(1-(1+\delta)\lambda\big)^2}.$$
--
--   Applied to $\Phi_\eta = F + \eta\langle c,\cdot\rangle$, this is the contraction step of the inexact path-following analysis (Theorem 12).
--
--   Differences from the source:
--   - correction: F : K → ℝ self-concordant (Definition 4 states only the cubic inequality) → F self-concordant and divergent at the boundary of K (closed), with x⁺ ∈ int(K) in the conclusion; reason: without closedness the step can leave K: K = [0,1], F(x) = (x+0.2)² on (0,1), x = 0.1, exact step (δ = 0) gives λ = 0.424 < 1 and x⁺ = −0.2 ∉ K, so λ(x⁺) is undefined, and for the C^∞ extension F(x) = (x+0.2)² + 50x² on x < 0 it equals 1.98 > λ²/(1−λ)² = 0.54; [NN94]'s self-concordant functions, cited in Definition 4, are closed
--   - reading: H(x)⁻¹ in Δ(x) = −H(x)⁻¹∇F(x) → hypothesis: the Hessian is positive definite on int(K); reason: the Newton step presupposes an invertible Hessian ([NN94] nondegenerate barriers)
--   - encoding: δ < min{1/2, (1 − λ)/λ} → δ < 1/2 and δ·λ < 1 − λ; reason: equivalent for λ > 0, and the right reading of (1 − λ)/λ = +∞ at λ = 0
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 13, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_IPM

namespace PQNormIPM1352.Main

/-- **Lemma 13** (inexact Newton step; Pirazzini–Spielman, STOC 2027 #1352, p. 23). Let `F` be
self-concordant on `int(K)` (closed in the sense of [NN94]: it diverges at the boundary of `K`)
with invertible Hessian, `x ∈ int(K)` with `λ(x) = λ < 1`, and let `Δ̃` satisfy
`‖Δ̃ − Δ(x)‖_x ≤ δ ‖Δ(x)‖_x` for some `δ < min{1/2, (1 − λ)/λ}`. Then `x⁺ = x + Δ̃ ∈ int(K)` and
`λ(x⁺) ≤ (δλ + (1 + δ)λ²) / (1 − (1 + δ)λ)²`. -/
theorem lemma_13 {N : ℕ} (K : Set (Vec N)) (F : Vec N → ℝ) (hF : IsSelfConcordantFunction K F)
    (hdiv : DivergesAtBoundary K F) (hH : ∀ y ∈ interior K, (hessMat F y).PosDef)
    (x : Vec N) (hx : x ∈ interior K) (hdec : newtonDecrement F x < 1) (δ : ℝ) (hδ : δ < 1 / 2)
    (hδdec : δ * newtonDecrement F x < 1 - newtonDecrement F x) (Δt : Vec N)
    (hΔ : IsApproxNewtonStep F δ x Δt) :
    x + Δt ∈ interior K ∧
      newtonDecrement F (x + Δt) ≤
        (δ * newtonDecrement F x + (1 + δ) * newtonDecrement F x ^ 2) /
          (1 - (1 + δ) * newtonDecrement F x) ^ 2 := by sorry

end PQNormIPM1352.Main

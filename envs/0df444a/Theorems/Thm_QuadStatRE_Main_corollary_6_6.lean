-- Prove2me | Theorems.Thm_QuadStatRE_Main_corollary_6_6
-- name    : QuadStatRE.Main.corollary_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:56.606239+00:00
-- url     : https://prove2.me/theorems/ff0e5533-6f51-4595-a482-0aa9fc4e901a
-- title:
--   Corollary 6.6 — Λ_{M^⊗15}(A(W)) = P(τ(W)) and τ(A(W)) ≤ B(τ(W))
-- statement:
--   Let $W$ be an affine-symmetric leakage family on a finite alphabet $\Omega$ with mixture $M=\frac18\sum_{s\in G}W_s$, and let $M^{\otimes15}$ be the product of fifteen copies of $M$ on $\Omega^I$. Then
--   $$\Lambda_{M^{\otimes15}}(\mathcal A(W))=P(\tau(W)),\qquad\tau(\mathcal A(W))\le B(\tau(W)), \tag{6.9}$$
--   where $P$ is the counting polynomial (6.2) and $B(\theta)=(\sqrt{P(\theta)}-1)/(\sqrt8-1)$.
--
--   One RM step therefore maps $\tau$ to at most the explicit scalar function $B(\tau)$, which is what the rest of the analysis iterates.
--
--   Differences from the source:
--
--   - encoding: M^{⊗15} on the fifteen child transcripts → prodRef (mix W) : (Fin 15 → Ω) → ℝ, T ↦ ∏_k M(T_k); reason: the product distribution
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
--   - encoding: distributions on a finite set → nonnegative functions Ω → ℝ of total mass one (IsLaw / IsLeakageFamily); reason: finite distributions as probability vectors
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 31, Corollary 6.6, (6.9)

import Mathlib
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE

namespace QuadStatRE.Main

/-- Corollary 6.6 (Normalized `χ²`-information after an RM step), p. 31: for every affine-symmetric
child leakage family `W` with mixture `M`, `Λ_{M^{⊗15}}(A(W)) = P(τ(W))` and
`τ(A(W)) ≤ B(τ(W))` (6.9), where `M^{⊗15}` is the product of the fifteen child mixtures. -/
theorem corollary_6_6 {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) (hW : IsLeakageFamily W)
    (hA : AffineSymmetric W) :
    Lam (prodRef (mix W)) (amp W) = countPoly.eval (tau W) ∧ tau (amp W) ≤ B (tau W) := by sorry

end QuadStatRE.Main

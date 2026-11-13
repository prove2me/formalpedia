-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_design_list_recovery
-- name    : SubspaceEvasion312.Explicit.design_list_recovery
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:50.444182+00:00
-- url     : https://prove2.me/theorems/c5789128-c0bb-4451-85a4-5f4f779dc3af
-- title:
--   Theorem 15 (corrected: positive denominator) — design list recovery
-- statement:
--   Let $m>0$, $C\le(F_q^s)^m$ be a $\tau$-subspace design, $r,\ell\in\mathbb N$, and $\delta>0$. On the meaningful domain $\theta=\tau(r)+\delta>0$,
--
--   $$C\text{ is }\left(r,1-\theta,\ell,\left(\frac\ell\theta\right)^{\theta/\delta}\right)\text{ subspace list-recoverable}.$$
--
--   Both the error radius and the exact power are retained. The parameter $\tau$ is still permitted to be negative, and the zero code is allowed. This is the design-to-recovery estimate used for the logarithmic branch.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: the average over the code block length → positive block length m; reason: the source average 1/m presupposes nonzero block length; no positive rate or nonzero-code assumption is added
--   - correction: no lower-domain condition on τ(r)+δ → τ(r)+δ>0; reason: over F₂ take s=m=r=1, C={0}, τ(t)=-2, δ=ℓ=1, S₁={0}, U={0}; every printed assumption holds, but one recovered word exceeds the printed bound (1/(-1))^(-1)=-1; the minimal positive-denominator guard repairs this false statement
--   - encoding: a real output-list bound → the same nonnegative real power embedded into the extended nonnegative reals; reason: the corrected denominator and positive exponent make the expression nonnegative, including ℓ=0; this embedding changes no finite bound
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 15, printed p. 10 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_algebra

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Theorem 15 (corrected: positive denominator), printed p.10 (PDF p.11).
For the zero code over F2, tau=-2, epsilon=ell=1, the printed bound is -1
although the recovered list has one word. The minimal guard excludes this case. -/
theorem design_list_recovery {F : Type} [Field F] [Fintype F]
    {s m r ℓ : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (ε : ℝ) (hε : 0 < ε) (hden : 0 < τ r + ε) :
    ListRecoverable C r (1 - τ r - ε) ℓ
      (ENNReal.ofReal (((ℓ : ℝ) / (τ r + ε)) ^ ((τ r + ε) / ε))) := by sorry
end SubspaceEvasion312.Explicit

-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_zero_error_recovery
-- name    : SubspaceEvasion312.Explicit.zero_error_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:47.187711+00:00
-- url     : https://prove2.me/theorems/d4e4285e-4c55-4085-884b-18a3830bc718
-- title:
--   Corollary 16 — exact zero-error power and twice-the-list bound
-- statement:
--   Let $m>0$ and $C\le(F_q^s)^m$ be a $\tau$-subspace design. For every $r,\ell\in\mathbb N$, if $\tau(r)<1$, then
--
--   $$C\text{ is }(r,0,\ell,\ell^{1/(1-\tau(r))})\text{ subspace list-recoverable}.$$
--
--   At $\tau(r)=1$ the first bound is interpreted as $+\infty$ for positive $\ell$. Empty input lists have zero recovered words. The additional source clause remains exact: for every positive $\ell$ with $\tau(r)\le1/(1+\log_2\ell)$, the code is $(r,0,\ell,2\ell)$ subspace list-recoverable. This includes $\ell=1$, even at $\tau(r)=1$. These are the zero-error estimates for the logarithmic branch.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: the average over the code block length → positive block length m; reason: the source average 1/m presupposes nonzero block length; no positive rate or nonzero-code assumption is added
--   - reading: the singular exponent 1/(1-τ(r)) at τ(r)=1 → the exact finite power below one and the limiting bound +∞ at one for positive input-list size; reason: avoids Lean inverse-of-zero returning zero; the separate 2ℓ clause retains the nonvacuous singleton endpoint
--   - encoding: empty lists and log₂ℓ → ℓ=0 is handled separately with recovered-list bound zero; log₂ is used only for positive ℓ; reason: at positive block length the product of empty lists has no element, so no source instance is removed
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Corollary 16, printed p. 10 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_algebra

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Corollary 16, printed p.10 (PDF p.11). The singular exponent has value
+infinity at tau(r)=1; empty input lists have no recovered words at positive length. -/
theorem zero_error_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ (zeroErrorBound ℓ (τ r)) ∧
      (ℓ = 0 → ListRecoverable C r 0 ℓ 0) ∧
      (0 < ℓ → τ r ≤ 1 / (1 + log₂ (ℓ : ℝ)) → ListRecoverable C r 0 ℓ (2*ℓ)) := by sorry
end SubspaceEvasion312.Explicit

-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_small_design_recovery
-- name    : SubspaceEvasion312.Explicit.small_design_recovery
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:43.127462+00:00
-- url     : https://prove2.me/theorems/04377af1-7d2b-433d-ba93-f123629576c5
-- title:
--   Lemma 14 — small design parameter gives zero-error recovery
-- statement:
--   Let $m>0$ and let $C\le(F_q^s)^m$ be a $\tau$-subspace design. If $r>0$ and $\tau(r)<1/r$, then for every $\ell\in\mathbb N$,
--
--   $$C\text{ is }(r,0,\ell,\ell)\text{ subspace list-recoverable}.$$
--
--   The rank-zero case is also included without a reciprocal condition. No nonnegativity of $\tau$ or nonzero-rate assumption is imposed. This supplies the recovery guarantee of the quadratic branch.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: the average over the code block length → positive block length m; reason: the source average 1/m presupposes nonzero block length; no positive rate or nonzero-code assumption is added
--   - generalization: the reciprocal condition τ(r)<1/r → the same positive-r result, together with unconditional rank-zero recovery; reason: at rank zero only the zero vector can be recovered; for positive length empty lists recover nothing and nonempty singleton lists recover at most one vector
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Lemma 14, printed p. 10 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_algebra

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Lemma 14, printed p.10 (PDF p.11), with the trivial r=0 case explicit. -/
theorem small_design_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (hτ : r = 0 ∨ τ r < 1 / (r : ℝ)) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ ℓ := by sorry
end SubspaceEvasion312.Explicit

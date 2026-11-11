-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_condenser_recovery
-- name    : SubspaceEvasion312.Explicit.condenser_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:45.746213+00:00
-- url     : https://prove2.me/theorems/bebdbab0-3753-41b2-98d2-1799774a2591
-- title:
--   Lemma 12 — lossless condensers give zero-error list recovery
-- statement:
--   Let $C\le(F_q^s)^m$ be an additive code that is a lossless rank condenser up to rank $r$. Then, for every input list size $\ell\in\mathbb N$,
--
--   $$C\text{ is }(r,0,\ell,\ell)\text{ subspace list-recoverable}.$$
--
--   The guarantee ranges over every ambient linear subspace of dimension at most $r$ and every family of lists of size at most $\ell$. It includes rank zero and empty input lists. This transfers injective-coordinate information into the recovery property used by graph composition.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Lemma 12, printed p. 9 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_algebra

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Lemma 12, printed p.9 (PDF p.10). -/
theorem condenser_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (C : Code F s m) (hC : RankCondenser C r) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ ℓ := by sorry
end SubspaceEvasion312.Explicit

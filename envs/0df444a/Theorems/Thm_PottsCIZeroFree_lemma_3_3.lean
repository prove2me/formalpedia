-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_3_3
-- name    : PottsCIZeroFree.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:47.042106+00:00
-- url     : https://prove2.me/theorems/53eb59a6-0dd2-41f6-bd0c-eebd0f78aa12
-- title:
--   Lemma 3.3 — one-vertex comparison at $z=0$: $\widehat Z^{\tau^{y=a}}_G(0)\le q^\Delta\,\widehat Z^{\tau^{y=b}}_G(0)$
-- statement:
--   Let $q,\Delta$ be positive integers with $q\ge\Delta+1$ and put $H_*=q^\Delta$. For every finite simple graph $G$ of maximum degree at most $\Delta$, every pinning $\tau$, every free vertex $y\in V^\tau$ and all colors $a,b$,
--   $$\widehat Z^{\tau^{y=a}}_G(0)\le H_*\,\widehat Z^{\tau^{y=b}}_G(0).$$
--
--   The bound controls how much one vertex color can change the hard-coloring count, and is the additive-error input of the disc around $z=0$.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q, and 0 < Δ where no other hypothesis bounds Δ, as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.13 (PDF p.15), Lemma 3.3, display (20)

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree

/-- Lemma 3.3 (One-vertex comparison at z = 0) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.13 (PDF p.15).
Assume `q ≥ Δ + 1` and put `H∗ := q^Δ`. For every `G ∈ G_Δ`, every pinning `τ`, every
`y ∈ V^τ`, and all colors `a, b`, `Ẑ^{τ^{y=a}}_G(0) ≤ H∗ Ẑ^{τ^{y=b}}_G(0)` (20).

**Formalization Note.** `q, Δ` are positive integers (§2.1). -/
theorem lemma_3_3 (q Δ : ℕ) (hΔ : 0 < Δ) (hq : Δ + 1 ≤ q) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : MaxDegLE G Δ) (Λ : Set V) (τ : V → Fin q) (y : V) (hy : y ∉ Λ)
    (a b : Fin q) :
    normPinnedAt G (childSet Λ y) (childPin τ y a) 0 ≤
      (q : ℝ) ^ Δ * normPinnedAt G (childSet Λ y) (childPin τ y b) 0 := by sorry

end PottsCIZeroFree

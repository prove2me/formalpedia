-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_2_1
-- name    : PottsCIZeroFree.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:55.059196+00:00
-- url     : https://prove2.me/theorems/356f987f-7511-429b-b2c7-bb7f7226eaaa
-- title:
--   Lemma 2.1 — hard feasibility: $|L^\tau(u)|\ge\deg_{G^\tau}(u)+1$ and $\widehat Z^\tau_G(0)>0$ for $q\ge\Delta+1$
-- statement:
--   Let $q,\Delta$ be positive integers with $q\ge\Delta+1$. For every finite simple graph $G$ of maximum degree at most $\Delta$, every pinning $\tau$ and every free vertex $u\in V^\tau$,
--   $$|L^\tau(u)|\ge\deg_{G^\tau}(u)+1 .$$
--   Consequently $\widehat Z^\tau_G(0)>0$.
--
--   At $z=0$ only colorings with no monochromatic edge outside $G[\Lambda]$ contribute; the lemma says such colorings always exist, so the normalized child laws at $x=0$ are well defined.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q, and 0 < Δ where no other hypothesis bounds Δ, as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.8 (PDF p.10), Lemma 2.1

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree

/-- Lemma 2.1 (Hard feasibility) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.8 (PDF p.10).
Assume `q ≥ Δ + 1`. For every `G ∈ G_Δ`, every pinning `τ`, and every `u ∈ V^τ`,
`|L^τ(u)| ≥ deg_{G^τ}(u) + 1`. Consequently, `Ẑ^τ_G(0) > 0`.

**Formalization Note.** `G` is any simple graph on a finite type with maximum degree `≤ Δ`; the
pinning is any `Λ ⊆ V` with `τ : V → Fin q` read on `Λ`. `q, Δ` are positive integers (§2.1). -/
theorem lemma_2_1 (q Δ : ℕ) (hΔ : 0 < Δ) (hq : Δ + 1 ≤ q) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : MaxDegLE G Δ) (Λ : Set V) (τ : V → Fin q) :
    (∀ u, u ∉ Λ → freeDegree G Λ u + 1 ≤ (hardList G Λ τ u).ncard) ∧
      0 < normPinnedAt G Λ τ 0 := by sorry

end PottsCIZeroFree

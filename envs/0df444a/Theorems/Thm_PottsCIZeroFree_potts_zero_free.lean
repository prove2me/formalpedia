-- Prove2me | Theorems.Thm_PottsCIZeroFree_potts_zero_free
-- name    : PottsCIZeroFree.potts_zero_free
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:47.680205+00:00
-- url     : https://prove2.me/theorems/eb848492-4aba-4163-8dfc-87d04115c174
-- title:
--   Theorem 1.1 — Potts zero-freeness: $\widehat Z^\tau_G(q;z)\ne0$ on $\mathcal U_\varepsilon([0,1])$ for $q\ge 11\Delta/6$
-- statement:
--   Let $q,\Delta$ be integers with $\Delta\ge2$ and $q\ge11\Delta/6$. There exists $\varepsilon=\varepsilon(q,\Delta)>0$ such that, for every finite simple graph $G$ of maximum degree at most $\Delta$ and every pinning $\tau$,
--   $$\widehat Z^\tau_G(q;z)\ne0\qquad\text{for every } z\in\mathcal U_\varepsilon([0,1]).$$
--   In particular $Z_G(q;z)\ne0$ throughout this neighborhood. The same holds for the usual pinned partition function $Z^\tau_G$ whenever $\tau$ is proper on $G[\Lambda]$; otherwise its only zero in this neighborhood is at $z=0$, with multiplicity $m_G(\tau)$.
--
--   The theorem lowers the threshold for a complex zero-free neighborhood of the antiferromagnetic interval on all bounded-degree graphs to $q\ge 11\Delta/6$, and with Barvinok's interpolation gives an FPTAS for $Z_G(q;z)$ near $[0,1]$.
--
--   **Formalization Note** $q\ge11\Delta/6$ is $11\Delta\le6q$ in $\mathbb N$, the equality case included. $\varepsilon$ is chosen before the graph. The pinning is any $\Lambda\subseteq V$, including $\emptyset$ and $V$, with any $\tau$, proper or not; "$\tau$ proper on $G[\Lambda]$" is $m_G(\tau)=0$. The multiplicity is `Polynomial.rootMultiplicity 0` of $Z^\tau_G$.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V : Type; reason: every finite graph is isomorphic to one on a finite type in Type, and all quantities are invariant under relabeling
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: q ≥ 11Δ/6 with q, Δ integers → 11 * Δ ≤ 6 * q in ℕ; reason: the same integers, equality case included
--   - encoding: τ proper on G[Λ] → pinnedMono G Λ τ = 0; reason: proper on G[Λ] means no monochromatic edge in G[Λ]
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.2 (PDF p.4), Theorem 1.1

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree

/-- Theorem 1.1 (Potts zero-freeness) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.2 (PDF p.4). Let `q, Δ` be
integers with `Δ ≥ 2` and `q ≥ 11Δ/6`. There exists `ε = ε(q, Δ) > 0` such that, for every finite
simple graph `G` of maximum degree at most `Δ` and every pinning `τ`, `Ẑ^τ_G(q; z) ≠ 0` for
every `z ∈ U_ε([0, 1])`. In particular, `Z_G(q; z) ≠ 0` throughout this neighborhood. The same
holds for the usual pinned partition function whenever `τ` is proper on `G[Λ]`; otherwise, its
only zero in this neighborhood is at `z = 0`, with multiplicity `m_G(τ)`.

**Formalization Note.** `q ≥ 11Δ/6` is `11Δ ≤ 6q` in `ℕ`, the equality case included. `ε` is
chosen before the graph. The graph is any simple graph on a finite type in `Type`; the pinning
is any `Λ ⊆ V`, including `∅` and `V`, with any `τ`. "`τ` proper on `G[Λ]`" is `m_G(τ) = 0`. -/
theorem potts_zero_free (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ ≤ 6 * q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V), MaxDegLE G Δ →
        (∀ z ∈ nbhd ε (Set.Icc 0 1), (partitionPoly G q).eval z ≠ 0) ∧
        ∀ (Λ : Set V) (τ : V → Fin q),
            (∀ z ∈ nbhd ε (Set.Icc 0 1), (normPinnedPoly G Λ τ).eval z ≠ 0) ∧
            (pinnedMono G Λ τ = 0 →
              ∀ z ∈ nbhd ε (Set.Icc 0 1), (pinnedPoly G Λ τ).eval z ≠ 0) ∧
            (1 ≤ pinnedMono G Λ τ →
              (∀ z ∈ nbhd ε (Set.Icc 0 1), (pinnedPoly G Λ τ).eval z = 0 ↔ z = 0) ∧
              Polynomial.rootMultiplicity 0 (pinnedPoly G Λ τ) = pinnedMono G Λ τ) := by sorry

end PottsCIZeroFree

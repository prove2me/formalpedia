-- Prove2me | Theorems.Thm_PottsCIZeroFree_corollary_4_13
-- name    : PottsCIZeroFree.corollary_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:30.446964+00:00
-- url     : https://prove2.me/theorems/49af2fff-fa8e-4bac-9ea1-cf7cca16988e
-- title:
--   Corollary 4.13 — coupling input at $q=11\Delta/6$: a finite constant at $x=0$ and $12/(11\delta)$ on $[\delta,1]$
-- statement:
--   Let $q,\Delta$ be integers with $\Delta\ge2$ and $q=11\Delta/6$. Then $\mathcal G_\Delta$ satisfies coupling independence at $x=0$ with a finite constant $C_0\ge0$, and for every $\delta\in(0,1]$ it satisfies coupling independence on $[\delta,1]$ with constant $12/(11\delta)$.
--
--   At the threshold the positive-activity bound degenerates at $x=0$, so the endpoint needs a separate hard-coloring bound; the corollary supplies both inputs of Theorem 1.3 at $q=11\Delta/6$.
--
--   **Formalization Note** $q=11\Delta/6$ is $6q=11\Delta$ in $\mathbb N$. The paper proves the $x=0$ clause by citing Chen, Feng, Guo, Zhang and Zou [CFG+25, Theorem 20 and Proposition 22]; it is stated here as printed.
--
--   Differences from the source:
--   - encoding: a class 𝒢 of finite simple graphs → a predicate on graphs on Fin n for every n (GraphClass); reason: every finite graph is isomorphic to one on Fin n, Ẑ is invariant under relabeling, and a class closed under induced embeddings is closed under isomorphism
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: q = 11Δ/6 → 6 * q = 11 * Δ in ℕ; reason: the same integers
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.25 (PDF p.27), Corollary 4.13

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Corollary 4.13 (Coupling input at q = 11Δ/6) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.25 (PDF p.27). Let
`q, Δ` be integers with `Δ ≥ 2` and `q = 11Δ/6`. Then `G_Δ` satisfies coupling independence at
`x = 0` with a finite constant, and for every `δ ∈ (0, 1]` it satisfies coupling independence on
`[δ, 1]` with constant `12/(11δ)`.

**Formalization Note.** `q = 11Δ/6` is `6q = 11Δ` in `ℕ`. The paper proves the `x = 0` clause by
citing [CFG+25, Theorem 20 and Proposition 22]; it is stated here as printed. -/
theorem corollary_4_13 (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 6 * q = 11 * Δ) :
    (∃ C₀ : ℝ, 0 ≤ C₀ ∧ CouplingIndependent q (GDelta Δ) C₀ {0}) ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
        CouplingIndependent q (GDelta Δ) (12 / (11 * δ)) (Set.Icc δ 1) := by sorry

end PottsCIZeroFree

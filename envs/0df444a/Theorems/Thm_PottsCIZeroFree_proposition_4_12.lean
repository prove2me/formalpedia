-- Prove2me | Theorems.Thm_PottsCIZeroFree_proposition_4_12
-- name    : PottsCIZeroFree.proposition_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:42.747504+00:00
-- url     : https://prove2.me/theorems/38167f18-4bf5-4f55-bed3-9e365c7d60e8
-- title:
--   Proposition 4.12 — Vigoda-profile coupling: $W_{1,\mathrm{Ham}}\le 2(1-x)\Delta/(q-\frac{11}6(1-x)\Delta)$
-- statement:
--   Let $q,\Delta$ be positive integers with $\Delta\ge2$. For every finite simple graph $G$ of maximum degree at most $\Delta$, every pinning $\tau$, every $r\in V^\tau$, all $a,b\in[q]$ and every $x\in(0,1]$ with $q>\frac{11}{6}(1-x)\Delta$,
--   $$W_{1,\mathrm{Ham}}\bigl(\mu^{\tau^{r=a}}_{G,x},\mu^{\tau^{r=b}}_{G,x}\bigr)\le\frac{2(1-x)\Delta}{q-\frac{11}{6}(1-x)\Delta}.$$
--   If $q>11\Delta/6$, the bound also holds at $x=0$, where it reads $2\Delta/(q-\frac{11}6\Delta)$.
--
--   This is the coupling-independence bound on the whole interval where Vigoda's contraction holds.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: W_{1,Ham} on colorings of V^τ \ {r} → MarkovMixing.transportDist with the Hamming cost on colorings of the free vertices of the child pinning; reason: the inf over couplings of the expected cost, on the same state space
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.24 (PDF p.26), Proposition 4.12, display (36)

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Proposition 4.12 (Vigoda-profile coupling for newly pinned laws) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.24
(PDF p.26). Let `q, Δ` be positive integers with `Δ ≥ 2`. For every `G ∈ G_Δ`, every pinning
`τ`, every `r ∈ V^τ`, all `a, b ∈ [q]`, and every `x ∈ (0, 1]` satisfying `q > (11/6)(1 − x)Δ`,
`W_{1,Ham}(µ^{τ^{r=a}}_{G,x}, µ^{τ^{r=b}}_{G,x}) ≤ 2(1 − x)Δ / (q − (11/6)(1 − x)Δ)` (36).
If `q > 11Δ/6`, the bound (36) also holds at `x = 0`. -/
theorem proposition_4_12 (q Δ : ℕ) (hq : 0 < q) (hΔ : 2 ≤ Δ) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : MaxDegLE G Δ) (Λ : Set V) (τ : V → Fin q) (r : V) (hr : r ∉ Λ)
    (a b : Fin q) :
    (∀ x ∈ Set.Ioc (0 : ℝ) 1, (11 / 6 : ℝ) * (1 - x) * Δ < q →
      childW1 G Λ τ r a b x ≤ 2 * (1 - x) * Δ / (q - 11 / 6 * (1 - x) * Δ)) ∧
    ((11 / 6 : ℝ) * Δ < q →
      childW1 G Λ τ r a b 0 ≤ 2 * Δ / (q - 11 / 6 * Δ)) := by sorry

end PottsCIZeroFree

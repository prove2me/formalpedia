-- Prove2me | Theorems.Thm_PottsCIZeroFree_theorem_4_1
-- name    : PottsCIZeroFree.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:15.488901+00:00
-- url     : https://prove2.me/theorems/5f532ac7-b395-4025-9879-46a119e543f4
-- title:
--   Theorem 4.1 — Hamming coupling independence on $[0,1]$ for $q>11\Delta/6$, with constant $2/\gamma_0$
-- statement:
--   Let $q,\Delta$ be positive integers with $\Delta\ge2$ and $q>11\Delta/6$, and put
--   $$\gamma_0:=\frac q\Delta-\frac{11}6>0 .$$
--   Then, for every finite simple graph $G$ of maximum degree at most $\Delta$, every pinning $\tau$, every $x\in[0,1]$, every $r\in V^\tau$ and all $a,b\in[q]$, both child laws are well defined and
--   $$W_{1,\mathrm{Ham}}\bigl(\mu^{\tau^{r=a}}_{G,x},\mu^{\tau^{r=b}}_{G,x}\bigr)\le\frac{2(1-x)\Delta}{q-\frac{11}{6}(1-x)\Delta}\le\frac2{\gamma_0}.$$
--
--   This supplies the coupling input of Theorem 1.3 above Vigoda's threshold, with one constant on all of $[0,1]$.
--
--   **Formalization Note** $q>11\Delta/6$ is $11\Delta<6q$ in $\mathbb N$. Well-definedness, printed for $x=0$ ("both laws are well defined by Lemma 2.1"), is stated as the positivity of both normalizing constants for every $x\in[0,1]$.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: W_{1,Ham} on colorings of V^τ \ {r} → MarkovMixing.transportDist with the Hamming cost on colorings of the free vertices of the child pinning; reason: the inf over couplings of the expected cost, on the same state space
--   - generalization: "at x = 0 both laws are well defined" → both normalizing constants are positive for every x ∈ [0, 1]; reason: for x > 0 positivity is immediate (a nonempty sum of positive terms), so the x = 0 statement is the content and is the special case
--   - encoding: q > 11Δ/6 → 11 * Δ < 6 * q in ℕ; reason: the same integers
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.16 (PDF p.18), Theorem 4.1

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Theorem 4.1 (Hamming coupling independence on [0, 1]) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.16 (PDF p.18).
Let `q, Δ` be positive integers with `Δ ≥ 2` and `q > 11Δ/6`. Put `γ₀ := q/Δ − 11/6 > 0`. Then,
for every `G ∈ G_Δ`, every pinning `τ`, every `x ∈ [0, 1]`, every `r ∈ V^τ`, and all
`a, b ∈ [q]`,
`W_{1,Ham}(µ^{τ^{r=a}}_{G,x}, µ^{τ^{r=b}}_{G,x}) ≤ 2(1 − x)Δ / (q − (11/6)(1 − x)Δ) ≤ 2/γ₀`.
At `x = 0` both laws are well defined by Lemma 2.1.

**Formalization Note.** `q > 11Δ/6` is `11Δ < 6q` in `ℕ`. The well-definedness of both laws
(positive normalizing constants), printed after the display, is stated as a conclusion for every
`x ∈ [0, 1]`. -/
theorem theorem_4_1 (q Δ : ℕ) (hq : 0 < q) (hΔ : 2 ≤ Δ) (hqΔ : 11 * Δ < 6 * q) :
    0 < (q : ℝ) / Δ - 11 / 6 ∧
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), MaxDegLE G Δ →
      ∀ (Λ : Set V) (τ : V → Fin q), ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ r, r ∉ Λ → ∀ a b : Fin q,
        0 < normPinnedAt G (childSet Λ r) (childPin τ r a) x ∧
        0 < normPinnedAt G (childSet Λ r) (childPin τ r b) x ∧
        childW1 G Λ τ r a b x ≤ 2 * (1 - x) * Δ / (q - 11 / 6 * (1 - x) * Δ) ∧
        2 * (1 - x) * Δ / (q - 11 / 6 * (1 - x) * Δ) ≤ 2 / ((q : ℝ) / Δ - 11 / 6) := by sorry

end PottsCIZeroFree

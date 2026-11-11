-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_11
-- name    : PottsCIZeroFree.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:20.000099+00:00
-- url     : https://prove2.me/theorems/90139a9f-25a1-4f31-b391-e796ae419987
-- title:
--   Lemma 4.11 — soft path contraction: $nq\,\mathbb E[\mathrm{Ham}(X',Y')-1]\le\frac{11}6t\Delta-q$
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $\Delta$, $\tau$ a pinning and $x\in(0,1]$; put $t=1-x$ and $n=|V^\tau|\ge1$. Colorings $X,Y$ of $V^\tau$ at Hamming distance one admit a coupling $(X',Y')$ of one step of $K^{G,\tau}_x$ (Vigoda's profile) satisfying
--   $$nq\,\mathbb E[\mathrm{Ham}(X',Y')-1]\le\tfrac{11}{6}t\Delta-q .$$
--   In particular, if $q>\frac{11}{6}t\Delta$, then
--   $$\kappa_x=\frac{q-\frac{11}6t\Delta}{q}>0$$
--   and the soft kernel contracts Hamming distance by the factor $1-\kappa_x/n$: $W_{1,\mathrm{Ham}}(K^{G,\tau}_x(X,\cdot),K^{G,\tau}_x(Y,\cdot))\le(1-\kappa_x/n)\,\mathrm{Ham}(X,Y)$ for all colorings $X,Y$.
--
--   This extends Vigoda's flip contraction from hard colorings to every positive activity.
--
--   **Formalization Note** A coupling of one step is a distribution on pairs of colorings with marginals $K(X,\cdot)$ and $K(Y,\cdot)$.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - reading: "the soft kernel contracts Hamming distance by the factor 1 − κ_x/n" → W_{1,Ham}(K(X,·), K(Y,·)) ≤ (1 − κ_x/n) Ham(X, Y) for all X, Y; reason: the proof ends "path coupling along shortest paths extends the adjacent-state bound to all pairs", so the contraction is for all pairs
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q (and 0 < Δ) as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.24 (PDF p.26), Lemma 4.11, displays (34)–(35)

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent
import Definitions.Def_PottsCIZeroFree_softKernel

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.11 (Soft path contraction) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.24 (PDF p.26). For `G ∈ G_Δ`, a
pinning `τ`, and `x ∈ (0, 1]`, put `t = 1 − x` and `n = |V^τ| ≥ 1`. Colorings `X, Y` at Hamming
distance one admit a coupling `(X', Y')` of one step of `K^{G,τ}_x` satisfying
`nq E[Ham(X', Y') − 1] ≤ (11/6)tΔ − q` (34). In particular, if `q > (11/6)tΔ`, the soft kernel
contracts Hamming distance by the factor `1 − κ_x/n`, where `κ_x = (q − (11/6)tΔ)/q > 0` (35).

**Formalization Note.** `K^{G,τ}_x` is the soft flip kernel with Vigoda's profile (25). A
coupling of one step is a distribution on pairs with marginals `K(X, ·)` and `K(Y, ·)`.
"Contracts by the factor" is `W_{1,Ham}(K(X, ·), K(Y, ·)) ≤ (1 − κ_x/n) Ham(X, Y)` for all pairs
`X, Y` (the last line of the proof, p.24). `q, Δ` are positive (§2.1). -/
theorem lemma_4_11 (q Δ : ℕ) (hq : 0 < q) (hΔ : 0 < Δ) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : MaxDegLE G Δ) (Λ : Set V) (τ : V → Fin q) (x : ℝ)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) (hn : 1 ≤ Fintype.card {v // v ∉ Λ}) :
    (∀ X Y : {v // v ∉ Λ} → Fin q, ham X Y = 1 →
      ∃ π : ({v // v ∉ Λ} → Fin q) × ({v // v ∉ Λ} → Fin q) → ℝ,
        MarkovMixing.IsCoupling (pinnedSoftKernel vigodaProfile x G Λ τ X)
          (pinnedSoftKernel vigodaProfile x G Λ τ Y) π ∧
        (Fintype.card {v // v ∉ Λ} : ℝ) * q * ∑ p, π p * (ham p.1 p.2 - 1) ≤
          11 / 6 * (1 - x) * Δ - q) ∧
      ((11 / 6 : ℝ) * (1 - x) * Δ < q →
        0 < ((q : ℝ) - 11 / 6 * (1 - x) * Δ) / q ∧
        ∀ X Y : {v // v ∉ Λ} → Fin q,
          MarkovMixing.transportDist (fun X Y => ham X Y)
              (pinnedSoftKernel vigodaProfile x G Λ τ X)
              (pinnedSoftKernel vigodaProfile x G Λ τ Y) ≤
            (1 - (((q : ℝ) - 11 / 6 * (1 - x) * Δ) / q) / (Fintype.card {v // v ∉ Λ} : ℝ)) *
              ham X Y) := by sorry

end PottsCIZeroFree

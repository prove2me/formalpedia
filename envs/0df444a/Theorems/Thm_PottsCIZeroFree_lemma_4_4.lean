-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_4
-- name    : PottsCIZeroFree.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:33.438492+00:00
-- url     : https://prove2.me/theorems/0097189c-60a1-4778-9068-71114444baf8
-- title:
--   Lemma 4.4 — soft Potts as a random hard-coloring model: $\sigma\mid A$ is uniform on $\Omega_{F_A}$
-- statement:
--   Let $G$ be a finite simple graph, $\tau$ a pinning and $x\in(0,1]$. Let $\sigma\sim\mu^\tau_{G,x}$, and given $\sigma$ activate each satisfied inequality of $\mathcal E_\tau$ (the free edges and the individually labeled free–pinned edges) independently with probability $1-x$; let $A$ be the active set. Then, conditional on $A$, $\sigma$ is uniform on $\Omega_{F_A}$. That is, for every active set $A$ of positive probability and every coloring $\sigma$ of $V^\tau$,
--   $$\Pr[\sigma\mid A]=\frac{\mathbf 1[\sigma\in\Omega_{F_A}]}{|\Omega_{F_A}|}.$$
--
--   The lemma represents the soft Potts law as a mixture of uniform laws on hard list-coloring instances, on which the flip dynamics is analyzed.
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - generalization: G ∈ G_Δ (fixed at the start of §4.2) → any finite simple graph G; reason: the degree bound is not used; graphs in G_Δ are a special case
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q (and 0 < Δ) as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.18 (PDF p.20), Lemma 4.4; activation and $F_A$ on p.17

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent
import Definitions.Def_PottsCIZeroFree_softKernel

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.4 (Soft Potts as a random hard-coloring model) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.18
(PDF p.20). If `σ ∼ µ^τ_{G,x}` and `A` is sampled as above (each satisfied inequality of
`E_τ`, a free edge or an individually labeled free–pinned edge, activated independently with
probability `1 − x`, `x ∈ (0, 1]`), then `σ`, conditional on `A`, is uniform on `Ω_{F_A}`.

**Formalization Note.** The joint law of `(σ, A)` is `µ^τ_{G,x}(σ) · actProb(σ, A)`; the
statement is that for every `A` of positive probability the conditional law of `σ` is the
uniform law on the colorings feasible for `F_A = (V^τ, E_A, L_A)`. `q` is positive (§2.1). -/
theorem lemma_4_4 (q : ℕ) (hq : 0 < q) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Λ : Set V) (τ : V → Fin q) (x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1)
    (A : Finset (Sym2 {v // v ∉ Λ}) × Finset (FPEdge G Λ))
    (hA : 0 < ∑ σ, pinnedGibbs G Λ τ x σ * actProb (freeGraph G Λ) (fpLabel G Λ τ) x σ A) :
    ∀ σ, pinnedGibbs G Λ τ x σ * actProb (freeGraph G Λ) (fpLabel G Λ τ) x σ A /
        (∑ σ', pinnedGibbs G Λ τ x σ' * actProb (freeGraph G Λ) (fpLabel G Λ τ) x σ' A) =
      if IsFeasible (activeGraph (freeGraph G Λ) A.1) (activeList (fpLabel G Λ τ) A.2) σ then
        1 / (Set.ncard {σ' | IsFeasible (activeGraph (freeGraph G Λ) A.1)
          (activeList (fpLabel G Λ τ) A.2) σ'} : ℝ)
      else 0 := by sorry

end PottsCIZeroFree

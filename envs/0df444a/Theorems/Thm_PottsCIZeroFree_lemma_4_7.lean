-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_7
-- name    : PottsCIZeroFree.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:34.057793+00:00
-- url     : https://prove2.me/theorems/f115abfc-0225-4d27-bbcd-b848d1a67af8
-- title:
--   Lemma 4.7 — soft flip kernels are reversible for $\mu^\tau_{G,x}$, and irreducible when $\rho_1>0$
-- statement:
--   Let $G$ be a finite simple graph, $\tau$ a pinning, $\rho$ a flip profile and $x\in(0,1]$. Then $K^{G,\tau}_{x,\rho}$ is a Markov kernel on $[q]^{V^\tau}$ that is reversible with stationary law $\mu^\tau_{G,x}$:
--   $$\mu^\tau_{G,x}(\sigma)K^{G,\tau}_{x,\rho}(\sigma,\sigma')=\mu^\tau_{G,x}(\sigma')K^{G,\tau}_{x,\rho}(\sigma',\sigma)\quad\text{for all }\sigma,\sigma' .$$
--   If $\rho_1>0$, it is irreducible on $[q]^{V^\tau}$.
--
--   So the soft flip chain samples the pinned Potts law, which is what lets stationary comparison bound distances between Gibbs laws.
--
--   **Formalization Note** Reversibility is the published `MarkovMixing.DetailedBalance`, stationarity `IsStationary`, irreducibility `Irreducible` (every state reaches every state with positive probability in some number of steps).
--
--   Differences from the source:
--   - encoding: every finite simple graph G = (V, E) → a SimpleGraph on a finite type V; reason: same graphs; a finite vertex set is a finite type
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - generalization: G ∈ G_Δ (fixed at the start of §4.2) → any finite simple graph G; reason: the degree bound is not used; graphs in G_Δ are a special case
--   - encoding: K^{G,τ}_{x,ρ} is a kernel (Definition 4.6) → IsStochastic of the kernel matrix stated as the first conjunct; reason: the kernel is defined by a matrix formula, so its being a Markov kernel is stated rather than assumed
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q (and 0 < Δ) as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.18 (PDF p.20), Lemma 4.7

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent
import Definitions.Def_PottsCIZeroFree_softKernel

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.7 (Soft flip kernels) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.18 (PDF p.20). For every profile `ρ`
and `x ∈ (0, 1]`, `K^{G,τ}_{x,ρ}` is reversible with stationary law `µ^τ_{G,x}`. If `ρ_1 > 0`,
it is irreducible on `[q]^{V^τ}`.

**Formalization Note.** The kernel is the stochastic matrix `pinnedSoftKernel ρ x G Λ τ` on the
colorings of the free vertices; reversibility is detailed balance, irreducibility is the
published `MarkovMixing.Irreducible`. That it is a Markov kernel (Definition 4.6) is stated as
the first conjunct. `q` is positive (§2.1). -/
theorem lemma_4_7 (q : ℕ) (hq : 0 < q) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Λ : Set V) (τ : V → Fin q) (ρ : ℕ → ℝ) (hρ : IsProfile ρ) (x : ℝ)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    MarkovMixing.IsStochastic (pinnedSoftKernel ρ x G Λ τ) ∧
      MarkovMixing.DetailedBalance (pinnedSoftKernel ρ x G Λ τ) (pinnedGibbs G Λ τ x) ∧
      MarkovMixing.IsStationary (pinnedSoftKernel ρ x G Λ τ) (pinnedGibbs G Λ τ x) ∧
      (0 < ρ 1 → MarkovMixing.Irreducible (pinnedSoftKernel ρ x G Λ τ)) := by sorry

end PottsCIZeroFree

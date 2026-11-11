-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_9
-- name    : PottsCIZeroFree.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:25.596555+00:00
-- url     : https://prove2.me/theorems/05e05431-3004-4a46-8f22-216f88dfb07d
-- title:
--   Lemma 4.9 — one extra labeled free–pinned edge moves the soft kernel by at most $(1-x)R_\rho/(mq)$ in $W_{1,\mathrm{Ham}}$
-- statement:
--   Let a minus and a plus pinned system have the same free vertex set $W$, of size $m\ge1$, and the same labeled constraints except for one additional free–pinned edge in the plus system. Let $\rho$ be a flip profile with $R_\rho:=\sup_{s\ge1}s\rho_s<\infty$ and let $x\in(0,1]$. Their soft kernels $K_-$, $K_+$ satisfy
--   $$W_{1,\mathrm{Ham}}(K_-(\sigma,\cdot),K_+(\sigma,\cdot))\le\frac{(1-x)R_\rho}{mq}\qquad(\sigma\in[q]^W).$$
--   Moreover:
--   1. for hard list kernels, deleting one color from one list gives the bound $R_\rho/(mq)$ on colorings feasible for the smaller list;
--   2. adding $k$ labeled free–pinned edges multiplies the soft bound by $k$;
--   3. for hard list kernels, deleting $k$ colors from lists multiplies the hard bound by $k$.
--
--   This measures how much pinning a vertex perturbs one step of the dynamics.
--
--   **Formalization Note** A pinned system is a free graph on $W$ with a finite family of labels $(u,c)$; the plus system has the labels indexed by `Option ι` (one extra) or `ι ⊕ κ` with $|\kappa|=k$. $R$ is any upper bound of $s\rho_s$ ($s\ge1$): the bound for every such $R$ is the bound for $R_\rho$, and conversely. Deleting $k$ colors means lists $L'\subseteq L$ with $\sum_u|L_u\setminus L'_u|=k$.
--
--   Differences from the source:
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: R_ρ := sup_{s≥1} sρ_s < ∞ in the bound → any R with sρ_s ≤ R for all s ≥ 1, in the bound; reason: R_ρ is such an R, and the bound with R_ρ implies the bound for every R ≥ R_ρ, so the two statements are equivalent
--   - encoding: a pinned system (free vertex set, free graph, labeled free–pinned edges) → a SimpleGraph on a Fintype W with labels lab : ι → W × Fin q; reason: every such family of labels arises from a graph and a pinning (one pinned neighbor of color c per label), and conversely
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q (and 0 < Δ) as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.19 (PDF p.21), Lemma 4.9, display (24)

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent
import Definitions.Def_PottsCIZeroFree_softKernel

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.9 (Effect of adding one labeled free–pinned edge) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.19
(PDF p.21). Let a minus and a plus pinned system have the same free vertex set `W`, of size
`m ≥ 1`, and the same labeled constraints except for one additional free–pinned edge in the
plus system. For a profile `ρ` with `R_ρ := sup_{s≥1} sρ_s < ∞` and `x ∈ (0, 1]`, their soft
kernels satisfy `W_{1,Ham}(K−(σ, ·), K+(σ, ·)) ≤ (1 − x)R_ρ/(mq)` for `σ ∈ [q]^W` (24). For
hard list kernels, deleting one color from one list gives the bound `R_ρ/(mq)` on colorings
feasible for the smaller list. Adding `k` labeled free–pinned edges (for hard list kernels,
deleting `k` colors from lists) multiplies the respective bound by `k`.

**Formalization Note.** A pinned system is a free graph `E` on `W` with labeled constraints
`lab : ι → W × [q]`; the plus system adds one label (`Option ι`) or `k` labels (`ι ⊕ κ`,
`|κ| = k`). `R` is any upper bound of `sρ_s` (`s ≥ 1`); the bound for every such `R` is the
bound for `R_ρ`, and conversely. Deleting `k` colors means `L' ⊆ L` with `k` deleted pairs in
total. `q` is positive (§2.1). -/
theorem lemma_4_9 (q : ℕ) (hq : 0 < q) {W : Type*} [Fintype W] (m : ℕ)
    (hm : Fintype.card W = m) (hm1 : 1 ≤ m) (E : SimpleGraph W) {ι : Type*} [Fintype ι]
    (lab : ι → W × Fin q) (ρ : ℕ → ℝ) (hρ : IsProfile ρ) (R : ℝ)
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * ρ s ≤ R) :
    (∀ (e : W × Fin q) (x : ℝ), x ∈ Set.Ioc (0 : ℝ) 1 → ∀ σ : W → Fin q,
        MarkovMixing.transportDist (fun X Y => ham X Y) (softKernel ρ x E lab σ)
            (softKernel ρ x E (fun o : Option ι => o.elim e lab) σ) ≤
          (1 - x) * R / ((m : ℝ) * q)) ∧
      (∀ (L : W → Set (Fin q)) (u₀ : W) (c₀ : Fin q) (σ : W → Fin q),
        IsFeasible E (Function.update L u₀ (L u₀ \ {c₀})) σ →
        MarkovMixing.transportDist (fun X Y => ham X Y) (flipKernel ρ E L σ)
            (flipKernel ρ E (Function.update L u₀ (L u₀ \ {c₀})) σ) ≤
          R / ((m : ℝ) * q)) ∧
      (∀ (k : ℕ) (κ : Type) [Fintype κ], Fintype.card κ = k → ∀ (extra : κ → W × Fin q)
        (x : ℝ), x ∈ Set.Ioc (0 : ℝ) 1 → ∀ σ : W → Fin q,
        MarkovMixing.transportDist (fun X Y => ham X Y) (softKernel ρ x E lab σ)
            (softKernel ρ x E (Sum.elim lab extra) σ) ≤
          k * ((1 - x) * R / ((m : ℝ) * q))) ∧
      (∀ (k : ℕ) (L L' : W → Set (Fin q)), (∀ u, L' u ⊆ L u) →
        ∑ u, (L u \ L' u).ncard = k → ∀ σ : W → Fin q, IsFeasible E L' σ →
        MarkovMixing.transportDist (fun X Y => ham X Y) (flipKernel ρ E L σ)
            (flipKernel ρ E L' σ) ≤
          k * (R / ((m : ℝ) * q))) := by sorry

end PottsCIZeroFree

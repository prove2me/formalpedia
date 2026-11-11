-- Prove2me | Theorems.Thm_PottsCIZeroFree_theorem_1_3
-- name    : PottsCIZeroFree.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:07.056324+00:00
-- url     : https://prove2.me/theorems/3396626c-21ac-4f7c-a393-33df50584e02
-- title:
--   Theorem 1.3 — coupling independence implies zero-freeness of $\widehat Z^\tau_G$ on $\mathcal U_\varepsilon([0,1])$
-- statement:
--   Fix integers $q,\Delta$ with $\Delta\ge2$ and $q\ge\Delta+1$, and let $\mathcal G$ be a class of finite simple graphs of maximum degree at most $\Delta$ that is closed under taking induced subgraphs. Assume
--   1. $\mathcal G$ satisfies coupling independence at $x=0$ with a constant $C_0\ge0$;
--   2. for every $\delta\in(0,1]$ it satisfies coupling independence on $[\delta,1]$ with a finite constant $C_\delta\ge0$.
--
--   Then there is $\varepsilon>0$ such that, for every $G\in\mathcal G$ and every pinning $\tau$,
--   $$\widehat Z^\tau_G(z)\ne0\qquad\text{for every } z\in\mathcal U_\varepsilon([0,1]).$$
--   Consequently $Z^\tau_G(z)=z^{m_G(\tau)}\widehat Z^\tau_G(z)$ has no zeros in the same neighborhood except, when $m_G(\tau)\ge1$, a zero of multiplicity $m_G(\tau)$ at $z=0$.
--
--   This is the transfer theorem: a purely probabilistic coupling bound, uniform over the class, yields a complex zero-free neighborhood of the whole antiferromagnetic interval.
--
--   **Formalization Note** $\varepsilon$ may depend on the class. The consequence is stated in two cases: if $m_G(\tau)=0$ then $Z^\tau_G$ has no zero in $\mathcal U_\varepsilon([0,1])$; if $m_G(\tau)\ge1$ its zeros there are exactly $z=0$ and `rootMultiplicity 0` of $Z^\tau_G$ is $m_G(\tau)$.
--
--   Differences from the source:
--   - encoding: a class 𝒢 of finite simple graphs → a predicate on graphs on Fin n for every n (GraphClass); reason: every finite graph is isomorphic to one on Fin n, Ẑ is invariant under relabeling, and a class closed under induced embeddings is closed under isomorphism
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.3 (PDF p.5), Theorem 1.3

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Theorem 1.3 (Coupling independence implies zero-freeness) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.3
(PDF p.5). Fix integers `q, Δ` with `Δ ≥ 2` and `q ≥ Δ + 1`, and let `𝒢` be a class of finite
simple graphs of maximum degree at most `Δ` that is closed under taking induced subgraphs.
Assume (i) `𝒢` satisfies coupling independence at `x = 0` with constant `C₀`; (ii) for every
`δ ∈ (0, 1]` it satisfies coupling independence on `[δ, 1]` with a finite constant `C_δ`. Then
there is `ε > 0` such that, for every `G ∈ 𝒢` and every pinning `τ`, `Ẑ^τ_G(z) ≠ 0` for every
`z ∈ U_ε([0, 1])`. Consequently `Z^τ_G(z) = z^{m_G(τ)} Ẑ^τ_G(z)` has no zeros in the same
neighborhood except, when `m_G(τ) ≥ 1`, a zero of multiplicity `m_G(τ)` at `z = 0`.

**Formalization Note.** `ε` may depend on the class. `C₀, C_δ ∈ [0, ∞)`. -/
theorem theorem_1_3 (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : Δ + 1 ≤ q) (𝒢 : GraphClass)
    (hdeg : DegBounded 𝒢 Δ) (hind : ClosedInduced 𝒢) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hi : CouplingIndependent q 𝒢 C₀ {0})
    (hii : ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      CouplingIndependent q 𝒢 Cδ (Set.Icc δ 1)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G →
        ∀ (Λ : Set (Fin n)) (τ : Fin n → Fin q),
            (∀ z ∈ nbhd ε (Set.Icc 0 1), (normPinnedPoly G Λ τ).eval z ≠ 0) ∧
            (pinnedMono G Λ τ = 0 →
              ∀ z ∈ nbhd ε (Set.Icc 0 1), (pinnedPoly G Λ τ).eval z ≠ 0) ∧
            (1 ≤ pinnedMono G Λ τ →
              (∀ z ∈ nbhd ε (Set.Icc 0 1), (pinnedPoly G Λ τ).eval z = 0 ↔ z = 0) ∧
              Polynomial.rootMultiplicity 0 (pinnedPoly G Λ τ) = pinnedMono G Λ τ) := by sorry

end PottsCIZeroFree

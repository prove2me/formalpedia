-- Prove2me | Theorems.Thm_PottsCIZeroFree_proposition_3_4
-- name    : PottsCIZeroFree.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:17.300352+00:00
-- url     : https://prove2.me/theorems/0a09f677-f8c2-4177-98c8-7ca80db452f9
-- title:
--   Proposition 3.4 — Potts disc around $z=0$: $\widehat Z^\tau_G(z)\ne0$ for $|z|<\rho_0(q,\Delta,C_0)$
-- statement:
--   Fix integers $q,\Delta$ with $\Delta\ge2$ and $q\ge\Delta+1$, and let $C_0\in[0,\infty)$. There is $\rho_0=\rho_0(q,\Delta,C_0)>0$ such that, for every class $\mathcal G\subseteq\mathcal G_\Delta$ closed under taking induced subgraphs and satisfying $C_0$-coupling independence at $x=0$,
--   $$\widehat Z^\tau_G(z)\ne0\qquad(|z|<\rho_0)$$
--   for every $G\in\mathcal G$ and every pinning $\tau$.
--
--   This is the zero-free disc at the hard-constraint endpoint, where some weights vanish and the positive-activity argument does not apply.
--
--   **Formalization Note** $\rho_0$ is chosen before the class.
--
--   Differences from the source:
--   - encoding: a class 𝒢 of finite simple graphs → a predicate on graphs on Fin n for every n (GraphClass); reason: every finite graph is isomorphic to one on Fin n, Ẑ is invariant under relabeling, and a class closed under induced embeddings is closed under isomorphism
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.13 (PDF p.15), Proposition 3.4

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Proposition 3.4 (Potts disc around z = 0) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.13 (PDF p.15).
Fix integers `q, Δ` with `Δ ≥ 2` and `q ≥ Δ + 1`, let `C₀ ∈ [0, ∞)`, and let `𝒢 ⊆ G_Δ` be
closed under taking induced subgraphs and satisfy `C₀`-coupling independence at `x = 0`. There
is `ρ₀ = ρ₀(q, Δ, C₀) > 0` such that `Ẑ^τ_G(z) ≠ 0` for `|z| < ρ₀`, for every `G ∈ 𝒢` and every
pinning `τ`.

**Formalization Note.** `ρ₀` is chosen before the class `𝒢`. -/
theorem proposition_3_4 (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : Δ + 1 ≤ q) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ 𝒢 : GraphClass, DegBounded 𝒢 Δ → ClosedInduced 𝒢 →
        CouplingIndependent q 𝒢 C₀ {0} →
        ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G →
          ∀ (Λ : Set (Fin n)) (τ : Fin n → Fin q), ∀ z : ℂ, ‖z‖ < ρ₀ →
            (normPinnedPoly G Λ τ).eval z ≠ 0 := by sorry

end PottsCIZeroFree

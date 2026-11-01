-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_property_15_1_1
-- name    : WildeQIT.Schumacher.property_15_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:45.995889+00:00
-- url     : https://prove2.me/theorems/699c5e37-2b24-4a3f-95b0-db541d2dd969
-- title:
--   Property 15.1.1 (Unit Probability): $\mathrm{Tr}\{\Pi^\delta_{A^n}\rho^{\otimes n}\} \ge 1-\varepsilon$ for large $n$
-- statement:
--   Let $\rho_A$ be a density operator on a finite-dimensional space with spectral decomposition $\rho = \sum_x p_X(x)|x\rangle\langle x|$, and let $\Pi^\delta_{A^n}$ be the corresponding $\delta$-typical projector. For every $\varepsilon \in (0,1)$ and every $\delta > 0$ there is an $N$ such that for all $n \ge N$
--
--   $$
--   \mathrm{Tr}\{\Pi^\delta_{A^n}\,\rho^{\otimes n}\} \ge 1 - \varepsilon .
--   $$
--
--   So the typical subspace measurement of $\rho^{\otimes n}$ finds the state typical with probability tending to one. This is the property that makes Schumacher's encoder succeed.
--
--   **Formalization Note** $\mathrm{Tr}$ is the real part of the complex trace (real here). Typicality is weak (Definition 14.2.3), logarithms base 2.
--
--   Differences from the source:
--   - reading: "the typical projector of ρ" with an implicit spectral decomposition → every spectral decomposition (U, p) of ρ; reason: the book fixes some decomposition (15.2) without naming it, and the claim is made for any of them.
--   - reading: weak or strong typicality → weak typicality (Definition 14.2.3); reason: the book states the property for either notion without distinguishing notation; Chapter 18 uses the typical set of §14.4, which is weak.
--   - encoding: "sufficiently large n" → ∃ N, ∀ n ≥ N; reason: Lean convention.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 15.1.1, eq. (15.17), p. 467

import Definitions.Def_WildeQIT_Schumacher_IsSpectralDecomposition
import Definitions.Def_WildeQIT_Schumacher_typicalProjector
import Definitions.Def_WildeQIT_Schumacher_tensorPow

namespace WildeQIT.Schumacher

/-- **Property 15.1.1 (Unit Probability)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 467, eq. (15.17)): the probability that the state `ρ^{⊗n}` is in the
typical subspace approaches one, `Tr{Π^δ_{Aⁿ} ρ^{⊗n}} ≥ 1 − ε` for all `ε ∈ (0, 1)`, `δ > 0` and
sufficiently large `n`, where `Π^δ_{Aⁿ}` is the typical projector of Definition 15.1.3.

**Formalization Note.** The typical projector is taken with respect to an arbitrary spectral
decomposition `ρ = U diag(p) U†` (eq. (15.2)); this hypothesis already makes `ρ` a density
operator. `Tr{·}` is the real part of the complex trace (the trace is real here). "Sufficiently
large `n`" is `∃ N, ∀ n ≥ N`. Weak typicality, logarithms base 2. -/
theorem property_15_1_1 {a : Type} [Fintype a] [DecidableEq a] (ρ U : Matrix a a ℂ)
    (p : FinDist a) (hU : IsSpectralDecomposition ρ U p) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
      1 - ε ≤ (typicalProjector U p n δ * tensorPow n ρ).trace.re := by sorry

end WildeQIT.Schumacher

-- Prove2me | Theorems.Thm_ROLDescent_definition_2_1_gap_iff
-- name    : ROLDescent.definition_2_1_gap_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:10.798864+00:00
-- url     : https://prove2.me/theorems/32e22b30-492a-460e-a751-7a1e25de7df8
-- title:
--   Definition 2.1, (6) — $\mathrm{gap}(A)\ge\gamma$ iff $\mathcal E(f)\ge\gamma\,\mathrm{dist}(f,\ker A)^2$
-- statement:
--   Let $A \succeq 0$ be a self-adjoint operator on a finite-dimensional complex Hilbert space $\mathcal H$ with $\mathcal N = \ker A$ and $\mathcal N^\perp \ne \{0\}$, and let $\mathcal E(f) = \langle f, A f\rangle$. For every $\gamma \ge 0$,
--
--   $$\mathrm{gap}(A) \ge \gamma \iff \mathcal E(f) \ge \gamma\, \mathrm{dist}(f, \mathcal N)^2 \ \text{ for every } f \in \mathcal H .$$
--
--   This is the form in which spectral gaps are compared with energy inequalities throughout the paper.
--
--   Differences from the source:
--   - encoding: gap(A) = min over 0 ≠ f ∈ N^⊥ of the Rayleigh quotient → specGap A, the sInf of these Rayleigh quotients; reason: the infimum is attained for positive A in finite dimension
--   - encoding: dist(f, N) → Metric.infDist f (ker A); reason: the distance of the specified inner product norm
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Definition 2.1, eqs. (5)–(6), p.9 (PDF 9)

import Mathlib
import Definitions.Def_ROLDescent_specGap

namespace ROLDescent

open scoped InnerProductSpace

/-- **Definition 2.1, equivalence (6): gap(A) ≥ γ iff E(f) ≥ γ dist(f, ker A)².** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545),
Definition 2.1, eqs. (5)–(6), p.9 (PDF 9): "Let A ⪰ 0 be self-adjoint on H, and set N = ker A. If
N^⊥ ≠ {0}, define gap(A) = min_{0≠f∈N^⊥} ⟨f, Af⟩/‖f‖². (5) For γ ≥ 0, the bound gap(A) ≥ γ is
equivalent to E(f) ≥ γ dist(f, N)² for every f ∈ H, (6) where distance and orthogonality use the
specified inner product." With (4): E(f) = ⟨f, Af⟩.

**Formalization Note** `A ⪰ 0` self-adjoint is Mathlib's `IsPositive`; dist(f, N) is
`Metric.infDist f (ker A)`. Both directions are stated, under `N^⊥ ≠ {0}` (where gap is defined). -/
theorem definition_2_1_gap_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →L[ℂ] E) (hA : A.IsPositive)
    (hN : (LinearMap.ker (A : E →ₗ[ℂ] E))ᗮ ≠ ⊥) (γ : ℝ) (hγ : 0 ≤ γ) :
    γ ≤ specGap A ↔ ∀ f : E,
      γ * Metric.infDist f (LinearMap.ker (A : E →ₗ[ℂ] E) : Set E) ^ 2 ≤ RCLike.re ⟪f, A f⟫_ℂ := by sorry

end ROLDescent

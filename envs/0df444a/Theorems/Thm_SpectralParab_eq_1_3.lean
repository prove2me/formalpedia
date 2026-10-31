-- Prove2me | Theorems.Thm_SpectralParab_eq_1_3
-- name    : SpectralParab.eq_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:04.686555+00:00
-- url     : https://prove2.me/theorems/6c42c13e-b0dc-4bca-95c2-ecd6ccac76a2
-- title:
--   (1.3): $\operatorname{dist}(X,\operatorname{dom}g)=\operatorname{dist}(\lambda(X),\operatorname{dom}\theta)$ for spectral functions
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be symmetric and $g=\theta\circ\lambda$ the spectral function of (1.1). For every $X\in\mathbf S^n$,
--   $$\operatorname{dist}(X,\operatorname{dom}g)=\operatorname{dist}(\lambda(X),\operatorname{dom}\theta).$$
--   This identity, cited from [9, Proposition 2.3], says that the metric subregularity condition needed for second-order chain rules holds automatically for the composite $\theta\circ\lambda$.
--
--   **Formalization Note** `Metric.infDist` (the distance to the empty set is $0$ on both sides).
--
--   Differences from the source:
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: dist(x, C), the distance from a point to a set → Metric.infDist, which is 0 when C is empty; reason: dom g is empty exactly when dom θ is empty, so both sides take that value together; on nonempty sets it is the paper's distance
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, (1.3), p.2

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, (1.3), p.2 (cited from [9, Proposition 2.3]). For a spectral function
`g = θ ∘ λ` with `θ` symmetric ((1.1)) and every `X ∈ Sⁿ`,
`dist(X, dom g) = dist(λ(X), dom θ)`.
**Formalization Note.** `Metric.infDist` is the distance to a set (`0` to the empty set, on both
sides alike). θ symmetric is part of the representation (1.1), not an added hypothesis. -/
theorem eq_1_3 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ) (X : SymMat (Fin n)) :
    Metric.infDist X (dom (specFn θ)) = Metric.infDist (lam X) (dom θ) := by sorry

end SpectralParab

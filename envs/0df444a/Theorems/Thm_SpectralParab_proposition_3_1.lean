-- Prove2me | Theorems.Thm_SpectralParab_proposition_3_1
-- name    : SpectralParab.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:31.386829+00:00
-- url     : https://prove2.me/theorems/50b78360-4fef-4e09-a7dd-b36805cbb97d
-- title:
--   Proposition 3.1: $\operatorname{dist}(x,\operatorname{dom}\theta)=\operatorname{dist}(\operatorname{Diag}(x),\operatorname{dom}g)$
-- statement:
--   Let $g=\theta\circ\lambda$ be a spectral function with $\theta$ symmetric (1.1). For every $x\in\mathbb R^n$,
--   $$\operatorname{dist}(x,\operatorname{dom}\theta)=\operatorname{dist}(\operatorname{Diag}(x),\operatorname{dom}g).\tag{3.5}$$
--   It is the counterpart of (1.3) for symmetric functions, used to pass second-order properties from $g$ to $\theta$.
--
--   Differences from the source:
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: dist(x, C), the distance from a point to a set → Metric.infDist, which is 0 when C is empty; reason: dom g is empty exactly when dom θ is empty, so both sides take that value together; on nonempty sets it is the paper's distance
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 3.1, (3.5), p.7

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 3.1, (3.5), p.7. For a spectral function `g = θ ∘ λ` with
`θ` symmetric ((1.1)) and every `x ∈ ℝⁿ`, `dist(x, dom θ) = dist(Diag(x), dom g)`.
**Formalization Note.** `Metric.infDist`; θ symmetric is part of (1.1). -/
theorem proposition_3_1 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ) (x : Rn n) :
    Metric.infDist x (dom θ) = Metric.infDist (Diag x) (dom (specFn θ)) := by sorry

end SpectralParab

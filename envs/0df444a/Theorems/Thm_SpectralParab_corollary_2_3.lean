-- Prove2me | Theorems.Thm_SpectralParab_corollary_2_3
-- name    : SpectralParab.corollary_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:17.07667+00:00
-- url     : https://prove2.me/theorems/43ff9bc7-9332-4d2a-bdee-4040244a7a14
-- title:
--   Corollary 2.3: $\lambda(X+tH+\tfrac12t^2W+o(t^2))=\lambda(X)+t\lambda'(X;H)+\tfrac12t^2\lambda''(X;H,W)+o(t^2)$
-- statement:
--   Let $X,H,W\in\mathbf S^n$. The one-sided limits $\lambda'(X;H)$ and $\lambda''(X;H,W)$ exist, and for every $r(t)=o(t^2)$ in $\mathbf S^n$, as $t\downarrow0$,
--   $$\lambda\big(X+tH+\tfrac12t^2W+r(t)\big)=\lambda(X)+t\lambda'(X;H)+\tfrac12t^2\lambda''(X;H,W)+o(t^2).\tag{2.14}$$
--   This vector expansion is what the parabolic chain rules of §4 rest on.
--
--   Differences from the source:
--   - encoding: “Assume that X has the eigenvalue decomposition (2.1) for some U ∈ Oⁿ(X)” → no such hypothesis; reason: every X ∈ Sⁿ has one (p.3), so the hypothesis excludes nothing
--   - reading: “λ(X + tH + ½t²W + o(t²)) = … + o(t²)” → the limits λ′, λ″ exist, and the expansion holds for every r(t) = o(t²); reason: the o(t²) inside λ is an arbitrary such term, and λ″ is only defined when its limit exists (p.5)
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Corollary 2.3, (2.14), p.5

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Corollary 2.3, (2.14), p.5. For `X, H, W ∈ Sⁿ`: the one-sided limits
`λ'(X; H)` and `λ''(X; H, W)` exist, and for every `r(t) = o(t²)` in `Sⁿ`,
`λ(X + tH + ½t²W + r(t)) = λ(X) + t λ'(X; H) + ½ t² λ''(X; H, W) + o(t²)` as `t ↓ 0`.
**Formalization Note.** The page's hypothesis "X has the eigenvalue decomposition (2.1) for some
U ∈ Oⁿ(X)" holds for every `X ∈ Sⁿ` (p.3) and is omitted. Existence of the limits is stated as
convergence of the difference quotients to `lamDir` and `lamDir2`. -/
theorem corollary_2_3 {n : ℕ} (X H W : SymMat (Fin n)) :
    Tendsto (fun t : ℝ => t⁻¹ • (lam (X + t • H) - lam X)) (𝓝[>] 0) (𝓝 (lamDir X H)) ∧
    Tendsto (fun t : ℝ => (2 / t ^ 2) • (lam (X + t • H + (t ^ 2 / 2) • W) - lam X - t • lamDir X H))
      (𝓝[>] 0) (𝓝 (lamDir2 X H W)) ∧
    ∀ r : ℝ → SymMat (Fin n), r =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ 2) →
      (fun t : ℝ => lam (X + t • H + (t ^ 2 / 2) • W + r t) - lam X - t • lamDir X H
        - (t ^ 2 / 2) • lamDir2 X H W) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ 2) := by sorry

end SpectralParab

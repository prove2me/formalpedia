-- Prove2me | Theorems.Thm_SpectralParab_proposition_2_2
-- name    : SpectralParab.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:12.389816+00:00
-- url     : https://prove2.me/theorems/91b9f09a-a23e-46e4-b679-590c400ccd3d
-- title:
--   Proposition 2.2 with (2.13): second-order expansion of eigenvalue functions and the formula for $\lambda''_i(X;H,W)$
-- statement:
--   Let $X\in\mathbf S^n$, $U\in O^n(X)$, $H,W\in\mathbf S^n$, and $i$ an index with $i\in\alpha_m$ ($\mu_m=\lambda_i(X)$). Let $Q_m\in O^{|\alpha_m|}(U_{\alpha_m}^\top HU_{\alpha_m})$ be as in (2.10), $\beta^m_j\ni\ell_i(X)$ as in (2.12), $R_{mj}=(Q_m)_{\beta^m_j}$, and $\ell'_i=\ell'_i(X,H)$. For every $Y(t)=X+tH+\tfrac12t^2W+o(t^2)\in\mathbf S^n$, as $t\downarrow0$,
--   $$\lambda_i(Y(t))=\lambda_i(X)+t\lambda_{\ell_i}(U_{\alpha_m}^\top HU_{\alpha_m})+\tfrac12t^2\lambda_{\ell'_i}\Big(R_{mj}^\top U_{\alpha_m}^\top\big(W+2H(\mu_mI-X)^\dagger H\big)U_{\alpha_m}R_{mj}\Big)+o(t^2).$$
--   Moreover (2.13) the limit $\lambda''_i(X;H,W)$ exists and
--   $$\lambda''_i(X;H,W)=\lambda_{\ell'_i}\Big(R_{mj}^\top U_{\alpha_m}^\top\big(W+2H(\mu_mI-X)^\dagger H\big)U_{\alpha_m}R_{mj}\Big).$$
--   The block formula is used directly in Proposition 5.6(b) and in the proof of Theorem 5.8, where $Q_m$ is replaced by the matrices $\widehat Q_m$ of (5.22).
--
--   **Formalization Note** The $o(t^2)$ perturbation is an arbitrary $r:\mathbb R\to\mathbf S^n$ with $r(t)=o(t^2)$ as $t\downarrow0$. The statement holds for every $Q_m$ of (2.10).
--
--   Differences from the source:
--   - generalization: Proposition 2.2 states the expansion only → the expansion together with existence of λ″_i(X;H,W) and its formula (2.13); reason: (2.13) is the consequence the paper draws on the same page; the first conjunct is the printed proposition
--   - reading: Q_m and β^m_j “taken from (2.10) and (2.12)” → every Q_m ∈ O^{|α_m|}(U_{α_m}ᵀHU_{α_m}); reason: (2.10) only says such a Q_m is found; the proof of Theorem 5.8 uses the expansion for another choice (5.22), so it must hold for all
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - reading: Y(t) := X + tH + ½t²W + o(t²) → the expansion holds for every r(t) = o(t²) in Sⁿ as t ↓ 0; reason: the o(t²) inside Y(t) is an arbitrary such term; this is the stronger reading
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: Z† the Moore–Penrose inverse → SunNLSDP.Equiv.pinv, the functional calculus cfc (·⁻¹) of a symmetric matrix; reason: every Z† in this statement has Z = µ_m I − X symmetric, and on symmetric matrices pinv satisfies the four Penrose equations
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 2.2, p.5, and (2.13), p.5

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 2.2, p.5 (second-order expansion of eigenvalue functions,
from Torki [28, Proposition 2.2]), together with (2.13), p.5. Let `X ∈ Sⁿ`, `U ∈ Oⁿ(X)`,
`H, W ∈ Sⁿ`, `i` an index in the block `α_m` (`μ_m = λᵢ(X)`), `B = U_{α_m}ᵀ H U_{α_m}`, any
`Q_m ∈ O^{|α_m|}(B)` as in (2.10), `β^m_j ∋ ℓᵢ(X)` the block of (2.11)–(2.12), `R_{mj} = (Q_m)_{β^m_j}`
and `ℓ'ᵢ(X, H)` the position of `ℓᵢ(X)` in `β^m_j`. Then for every `r(t) = o(t²)` in `Sⁿ`, with
`Y(t) = X + tH + ½t²W + r(t)`,
`λᵢ(Y(t)) = λᵢ(X) + t λ_{ℓᵢ}(B) + ½ t² λ_{ℓ'ᵢ}(R_{mj}ᵀ U_{α_m}ᵀ (W + 2H(μ_m I − X)†H) U_{α_m} R_{mj}) + o(t²)`
as `t ↓ 0`; and (2.13): the limit `λ''ᵢ(X; H, W)` exists and equals that `λ_{ℓ'ᵢ}(…)`.
**Formalization Note.** 0-based indices; `eqBlock` and `posIn` give `β^m_j` and `ℓ'ᵢ`; `colsOf Q β`
is `R_{mj}`. The statement holds for every such `Q_m`. The λ''-quotient is written with
`lamDir X H i` (= `λ'ᵢ(X; H)`, a limit). -/
theorem proposition_2_2 {n : ℕ} (X : SymMat (Fin n)) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ On X) (H W : SymMat (Fin n)) (r : ℝ → SymMat (Fin n))
    (hr : r =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ 2)) (i : Fin n)
    (Q : Matrix (Fin (alpha X i).card) (Fin (alpha X i).card) ℝ)
    (hQ : Q ∈ OrthDiag (blockMat U X i H.toMat)) :
    let B := blockMat U X i H.toMat
    let β := eqBlock (eigVec B) (ell X i)
    let R := colsOf Q β
    let val := eigVec (Rᵀ * blockMat U X i
        (W.toMat + (2 : ℝ) • (H.toMat * pinv (shiftMat X i) * H.toMat)) * R)
        (posIn β (ell X i) (mem_eqBlock_self _ _))
    ((fun t : ℝ => lam (X + t • H + (t ^ 2 / 2) • W + r t) i - lam X i - t * eigVec B (ell X i)
        - t ^ 2 / 2 * val) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ 2)) ∧
    Tendsto (fun t : ℝ => (2 / t ^ 2) *
        (lam (X + t • H + (t ^ 2 / 2) • W) i - lam X i - t * lamDir X H i)) (𝓝[>] 0) (𝓝 val) ∧
    lamDir2 X H W i = val := by sorry

end SpectralParab

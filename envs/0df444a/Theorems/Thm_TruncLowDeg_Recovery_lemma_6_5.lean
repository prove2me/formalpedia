-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_6_5
-- name    : TruncLowDeg.Recovery.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:24.666566+00:00
-- url     : https://prove2.me/theorems/45defa4e-f1a5-408e-a071-0e136ae632f3
-- title:
--   Lemma 6.5 — the least-squares affine fit $\hat s_j$ recovers $\Sigma^{-1}$ and $\Sigma^{-1}\mu$ up to $d^{O(k)}\|p_js_j-q_j\|_{L^2(U)}$
-- statement:
--   In the setting of Theorem 6.1 let $(p_j,q_j)\in\mathbb R[x]_{\le3k}\times\mathbb R[x]_{\le4k}$ be a solution to (14), let $\hat s_j=\arg\min_{r\in\mathbb R[x]_{\le1}}\|p_jr-q_j\|_{L^2(U)}$ and write $\hat s_j(x)=\hat s_j^0+\sum_{i=1}^d\hat s_j^ix_i$. Then
--   $$\big|-\hat s_j^0-(\Sigma^{-1}\mu)_j\big|\le d^{O(k)}\,\|p_js_j-q_j\|_{L^2(U)},\qquad \big|\hat s_j^i-(\Sigma^{-1})_{ji}\big|\le d^{O(k)}\,\|p_js_j-q_j\|_{L^2(U)}\ \ \forall i.$$
--   Formally: one universal $C$ such that, for algorithm constants with $c_\rho\ge1$ (so $\rho\ge1$), all $d,k\ge1$, $\alpha_0\in(0,1]$, $\varepsilon\in(0,1)$, every $\mu$, $\Sigma\succ0$, finite list $\hat{\mathcal D}$, coordinate $j$, solution $(p_j,q_j)$ of (14) and minimizer $\hat s_j$, both bounds hold with $d^{Ck}$. It turns the polynomial guarantee of Proposition 6.4 into entrywise estimates of $\Sigma^{-1}$ and $\Sigma^{-1}\mu$.
--
--   Differences from the source:
--
--   - reading: d^{O(k)} → d^{C·k} with one universal constant C fixed before the algorithm constants and the instance; reason: the literal and stronger reading (as in Lemma 5.7; see finding I1 for d = 1)
--   - generalization: ρ = O(√d/α₀²) "with a sufficiently large implicit constant" → every algorithm constant vector with c_ρ ≥ 1, so ρ = c_ρ√d/α₀² ≥ 1; reason: the proof uses only ρ ≥ 1; the paper's sufficiently large ρ-constant is one such c_ρ, so it specializes
--   - generalization: the setting's µ, Σ and 𝒟̂ → arbitrary µ, Σ ≻ 0 and a finite list 𝒟̂ (no success or (15) hypothesis, as in the paper's statement); reason: the claim is deterministic in these objects; the setting's objects specialize it
--   - encoding: ŝ_j = arg min_{r ∈ ℝ[x]_{≤1}} ‖p_j r − q_j‖_{L²(U)} and its coefficients → any ŝ_j with `IsLSFit` (a minimizer of total degree ≤ 1); ŝ_j⁰ = `coeff 0`, ŝ_jⁱ = `coeff (single i 1)`, 0-based i; reason: the minimizer is unique when p_j ≠ 0, so stating the bound for every minimizer is the same claim
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 27, Lemma 6.5; proof pp. 31–32 (§6.1.3)

import Definitions.Def_TruncLowDeg_Recovery_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 6.5 (p. 27): coefficient recovery. One universal constant `C` (with `d^{O(k)}` read
as `d^{Ck}`) such that: for Algorithm 1's constants with `ρ`-constant at least `1` (so
`ρ ≥ 1`), `d, k ≥ 1`, `α₀ ∈ (0, 1]`, `ε ∈ (0, 1)`, any `µ`, `Σ ≻ 0`, `𝒟̂`, any coordinate `j`,
any solution `(p_j, q_j)` of (14) and any `ŝ_j ∈ argmin_{r ∈ ℝ[x]_{≤1}} ‖p_j r − q_j‖_{L²(U)}`
written `ŝ_j(x) = ŝ_j⁰ + ∑_i ŝ_jⁱ x_i`:
`|−ŝ_j⁰ − (Σ⁻¹µ)_j| ≤ d^{Ck} ‖p_j s_j − q_j‖_{L²(U)}` and
`|ŝ_jⁱ − (Σ⁻¹)_{ji}| ≤ d^{Ck} ‖p_j s_j − q_j‖_{L²(U)}` for every `i`. -/
theorem lemma_6_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : Consts, 1 ≤ c.rho →
      ∀ (d k : ℕ) (α₀ ε : ℝ), 1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → 0 < ε → ε < 1 →
      ∀ (μ : Vec d) (Sig : Mat d) (D : List (Vec d)), Sig.PosDef →
      ∀ (j : Fin d) (p q s : MvPolynomial (Fin d) ℝ),
        Solves14 k α₀ (rhoV c d α₀) (etaV c d k α₀ ε) c.q c.r D j p q →
        IsLSFit (rhoV c d α₀) p q s →
        |-coef0 s - (mulV Sig⁻¹ μ) j| ≤
            (d : ℝ) ^ (C * k) * L2U (rhoV c d α₀) (p * sPoly μ Sig j - q) ∧
          ∀ i : Fin d, |coefX s i - Sig⁻¹ j i| ≤
            (d : ℝ) ^ (C * k) * L2U (rhoV c d α₀) (p * sPoly μ Sig j - q) := by sorry

end TruncLowDeg.Recovery

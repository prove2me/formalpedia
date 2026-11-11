-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_proposition_7_9
-- name    : RandProdExp.TwoSided.proposition_7_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:21:48.80739+00:00
-- url     : https://prove2.me/theorems/993f2b33-7e0e-4095-8234-fb720b271e9e
-- title:
--   Proposition 7.9 — $\mathbb E\|G\|_{\mathrm{op}}\le3(1+\rho^{-1/2})$ for a normalized $k\times n$ Rademacher matrix with $k\ge\rho n$
-- statement:
--   Let $\rho\in(0,1)$ and let $k,n$ be integers with $k\ge\rho n$. For the normalized random Rademacher matrix $G=k^{-1/2}(\sigma_{r,c})_{r\in[k],c\in[n]}\in\mathbb R^{k\times n}$ with independent uniform signs,
--   $$\mathbb E_\sigma\big[\|G\|_{\mathrm{op}}\big]\le C_\rho=3\big(1+\rho^{-1/2}\big).$$
--   It bounds the factors $\|G_L\|_{\mathrm{op}}$, $\|G_R\|_{\mathrm{op}}$ in the decomposition of the plane-interaction matrix.
--
--   Differences from the source:
--   - encoding: ρ the constant of §6–§7 (ρ ∈ (0, 1), Lemma 7.1) → hypotheses 0 < ρ < 1; reason: standing range of ρ in the section
--   - encoding: expectation over independent uniform signs → uniform average over all sign matrices (signAvg); reason: the signs take finitely many values with equal probability
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 49, Proposition 7.9 (proved p. 54)

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_RealModel

namespace RandProdExp.TwoSided

/-- **Proposition 7.9** (p. 49). For a normalized random Rademacher matrix
`G = k^{−1/2} (σ_{r,c})_{r ∈ [k], c ∈ [n]} ∈ ℝ^{k × n}` with `k ≥ ρ n` (`ρ ∈ (0, 1)`), the expected
operator norm over the uniformly random signs satisfies `E[‖G‖_op] ≤ C_ρ = 3 (1 + ρ^{−1/2})`. -/
theorem proposition_7_9 (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k n : ℕ) (hk : ρ * n ≤ k) :
    signAvg (fun σ : Matrix (Fin k) (Fin n) ℤˣ => opNorm (normRademacher σ)) ≤
      3 * (1 + ρ ^ (-(1 / 2 : ℝ))) := by sorry

end RandProdExp.TwoSided

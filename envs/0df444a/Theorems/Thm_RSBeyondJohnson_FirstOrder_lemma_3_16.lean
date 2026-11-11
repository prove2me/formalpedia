-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_3_16
-- name    : RSBeyondJohnson.FirstOrder.lemma_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:31:53.204199+00:00
-- url     : https://prove2.me/theorems/93449083-e45f-4eb3-8811-c45f66a3d009
-- title:
--   Lemma 3.16 — finite coefficient–constraint margin above the first-order curve
-- statement:
--   Let $0<\rho<a<1$ with $a>a_1(\rho)$ and $n\ge2/\rho$, and take the parameters of (28). Then $0<\lambda_\partial<a_{\mathrm{cert}}/\rho$ and $\mathrm{Margin}^{(n)}_{\mathrm{int}}\ge\mathrm{Margin}_{\mathrm{int}}(\rho,a_{\mathrm{cert}},\lambda_\partial)$, where
--   $$\mathrm{Margin}_{\mathrm{int}}(\rho,a_{\mathrm{cert}},\lambda_\partial)=\begin{cases}\frac{\lambda_\partial}2\Big(\frac{(a_{\mathrm{cert}}-a_1(\rho))(a_{\mathrm{cert}}+a_1(\rho))}{\rho}-\lambda_\partial\Big),&0<\rho<\rho_c,\\[4pt]\frac{\lambda_\partial}2\Big[\frac{a_{\mathrm{cert}}^2}{\rho}-1+\frac{3(1-a_{\mathrm{cert}})^2}{4(2-\rho)}\Big],&\rho_c\le\rho<1,\end{cases}\qquad(29)$$
--   is positive. The parameters satisfy $0\le B_\partial\le B_{\mathrm{jet}}$ and
--   $$\nu_{\mathrm{coef}}-R_{\mathrm{loc}}(m,B_\partial)\ge m^3\mathrm{Margin}^{(n)}_{\mathrm{int}}-C_{\mathrm{rank}}m^2\ge\tfrac34m^3\mathrm{Margin}^{(n)}_{\mathrm{int}}>0.$$
--   For fixed $\rho$, with $\bar\eta_1=\eta_1+1/n=a-a_1(\rho)+1/n$: $m,B_\partial,B_{\mathrm{jet}}=O_\rho(\bar\eta_1^{-1})$ and $B_Z=O_\rho(\bar\eta_1^{-2})$, with one constant per $\rho$, uniform over $a$ and $n$. The positive margin is what makes the explainer of Corollary 3.17 exist.
--
--   Differences from the source:
--   - encoding: O_ρ(·) in m, B∂, B_jet = O_ρ(η̄₁⁻¹), B_Z = O_ρ(η̄₁⁻²) → ∀ ρ ∈ (0,1), ∃ C > 0 (chosen before every other variable), ∀ …: … ≤ C · (rate of the O); reason: the paper's convention (p. 5): the subscript lists the only parameters the hidden constant may depend on
--   - encoding: choose (m, B∂, B_jet, B_Z) by (28) → mParam, bDel, bJet, bZ ρ a n (definition Params); reason: the printed formulas of (28), as functions of (ρ, a, n) only
--   - encoding: (29) '… where Margin_int(ρ, a_cert, λ∂) = (29) is positive' → an equality with the branch formula (if ρ < ρ_c) and a separate positivity clause; reason: the two assertions of the sentence
--   - encoding: 0 ≤ B∂ → implicit (B∂ is a natural number); reason: bDel : ℕ
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 24, Lemma 3.16

import Mathlib
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 3.16 (Finite coefficient–constraint margin above the first-order curve)**, p. 24.
For every rate `0 < ρ < 1` there is a constant `C_ρ > 0` such that for all `ρ < a < 1` with
`a > a₁(ρ)` and all `n ≥ 2/ρ`: `0 < λ∂ < a_cert/ρ`; `Margin^(n)_int ≥ Margin_int(ρ, a_cert, λ∂)`,
which equals (29) on each branch and is positive; `0 ≤ B∂ ≤ B_jet`;
`ν_coef − R_loc(m, B∂) ≥ m³ Margin^(n)_int − C_rank m² ≥ 3m³ Margin^(n)_int/4 > 0`; and, with
`η̄₁ = η₁ + 1/n = a − a₁(ρ) + 1/n`, `m, B∂, B_jet ≤ C_ρ η̄₁⁻¹` and `B_Z ≤ C_ρ η̄₁⁻²`. -/
theorem lemma_3_16 :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ) (n : ℕ), ρ < a → a < 1 → a1 ρ < a → 2 / ρ ≤ (n : ℝ) →
        (0 < lamD ρ a ∧ lamD ρ a < aCert ρ a / ρ) ∧
        marginInt ρ (aCert ρ a) (lamD ρ a) ≤ marginN ρ a n ∧
        marginInt ρ (aCert ρ a) (lamD ρ a) =
          (if ρ < rhoC then
            lamD ρ a / 2 * ((aCert ρ a - a1 ρ) * (aCert ρ a + a1 ρ) / ρ - lamD ρ a)
          else
            lamD ρ a / 2 * (aCert ρ a ^ 2 / ρ - 1 + 3 * (1 - aCert ρ a) ^ 2 / (4 * (2 - ρ)))) ∧
        0 < marginInt ρ (aCert ρ a) (lamD ρ a) ∧
        bDel ρ a n ≤ bJet ρ a n ∧
        (mParam ρ a n : ℝ) ^ 3 * marginN ρ a n - cRank ρ a * (mParam ρ a n : ℝ) ^ 2 ≤
          nuCoef ρ a n - (rLoc (mParam ρ a n) (bDel ρ a n) : ℝ) ∧
        3 * (mParam ρ a n : ℝ) ^ 3 * marginN ρ a n / 4 ≤
          (mParam ρ a n : ℝ) ^ 3 * marginN ρ a n - cRank ρ a * (mParam ρ a n : ℝ) ^ 2 ∧
        0 < 3 * (mParam ρ a n : ℝ) ^ 3 * marginN ρ a n / 4 ∧
        (mParam ρ a n : ℝ) ≤ C / (a - a1 ρ + 1 / (n : ℝ)) ∧
        (bDel ρ a n : ℝ) ≤ C / (a - a1 ρ + 1 / (n : ℝ)) ∧
        (bJet ρ a n : ℝ) ≤ C / (a - a1 ρ + 1 / (n : ℝ)) ∧
        (bZ ρ a n : ℝ) ≤ C / (a - a1 ρ + 1 / (n : ℝ)) ^ 2 := by sorry

end RSBeyondJohnson.FirstOrder

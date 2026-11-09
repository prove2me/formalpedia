-- Prove2me | Theorems.Thm_PrettyGoodCriterion_theorem_7
-- name    : PrettyGoodCriterion.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:38:17.579513+00:00
-- url     : https://prove2.me/theorems/f28d7a2a-6fb8-473c-a465-387b8be00c52
-- title:
--   Theorem 7 — cq channel coding strong converse: $\Pr[\hat c=c]\le 2^{-n[R(\mathcal C)-\chi-2\varepsilon]}+4e^{-\varepsilon^2n/L_\sigma^2}$
-- statement:
--   Let $b\mapsto\sigma_b$ be a finite-dimensional binary-input output-symmetric cq channel with density outputs $\sigma_0,\sigma_1$. There is a constant $L_\sigma\ge1$, depending only on $\sigma_0$ and $\sigma_1$, such that:
--
--   1. for every $n$, every code $\mathcal C\subseteq\{0,1\}^n$ with $|\mathcal C|\ge2$, every $\varepsilon>0$ and every decoder POVM $\{D_c:c\in\mathcal C\}$ (positive semidefinite, $\sum_cD_c=I$), if $\hat c$ is obtained by measuring $\sigma_c$, $c$ uniform, then
--   $$\Pr[\hat c=c]\le2^{-n[R(\mathcal C)-\chi(\sigma_0,\sigma_1)-2\varepsilon]}+4\exp\!\big(-\varepsilon^2n/L_\sigma^2\big);\qquad(14)$$
--   2. consequently, a fixed rate gap forces exponential decay: if $R(\mathcal C)-\chi(\sigma_0,\sigma_1)\ge\Delta>0$, then for every such decoder
--   $$\Pr[\hat c=c]\le2^{-n\Delta/2}+4\exp\!\big(-\Delta^2n/(16L_\sigma^2)\big).$$
--
--   This is the strong converse of the classical–quantum channel coding theorem (after Winter and Ogawa–Nagaoka), specialized to binary-input output-symmetric channels, whose capacity is $\chi(\sigma_0,\sigma_1)$.
--
--   **Formalization Note** $L_\sigma$ is chosen before $n$, $\mathcal C$, $\varepsilon$ and the decoder. $\exp$ is the natural exponential, $2^{(\cdot)}$ a real power.
--
--   Differences from the source:
--   - reading: Consequently, any fixed positive rate gap above χ(σ₀, σ₁) forces the average decoding success probability to decay exponentially in n → for Δ > 0 and R(𝒞) − χ(σ₀, σ₁) ⩾ Δ: Pr[ĉ = c] ⩽ 2^{−nΔ/2} + 4 exp(−Δ²n/(16 L_σ²)) for every n, code and decoder; reason: the explicit form the proof gives for this sentence (p.71, ε = Δ/4)
--   - encoding: decoder POVM {D_c : c ∈ 𝒞} → a family of positive semidefinite matrices indexed by the subtype {c // c ∈ 𝒞} with sum I; reason: the same object
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Theorem 7, equation (14), p.17 (PDF 19); explicit form of the final assertion in the proof, Appendix A.4, p.71 (PDF 73)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_holevoUniform
import Definitions.Def_PrettyGoodCriterion_OutputSymmetric
import Definitions.Def_PrettyGoodCriterion_codePGM

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Theorem 7 (cq channel coding strong converse)**, Alrabiah–Guruswami, arXiv:2608.09347
(held version), p.17 (PDF 19), after [Win99, Theorem 13] and [ON99, Theorem 1]; proof in
Appendix A.4, pp.68–71 (PDF 70–73).

For a finite-dimensional binary-input output-symmetric cq channel with density outputs
`σ₀, σ₁` there is a constant `L_σ ⩾ 1`, depending only on `σ₀, σ₁`, such that for every code
`𝒞 ⊆ {0,1}ⁿ` (`|𝒞| ⩾ 2`, p.14), every `ε > 0` and every decoder POVM `{D_c : c ∈ 𝒞}`,
`Pr[ĉ = c] ⩽ 2^{−n[R(𝒞) − χ(σ₀,σ₁) − 2ε]} + 4 exp(−ε²n/L_σ²)` (14). Consequently, a fixed
positive rate gap `R(𝒞) − χ(σ₀, σ₁) ⩾ Δ > 0` forces exponential decay:
`Pr[ĉ = c] ⩽ 2^{−nΔ/2} + 4 exp(−Δ²n/(16 L_σ²))` (the explicit form in the proof, p.71).

**Formalization Note.** `L` is chosen before `n`, `𝒞`, `ε` and `D`. A decoder POVM is a family
of positive semidefinite matrices indexed by the codewords with sum `I`. `Pr[ĉ = c]` is
`decoderSuccess`, the average of `Re Tr(σ_c D_c)` over `c ∈ 𝒞`; `exp` is the natural
exponential. -/
theorem theorem_7 {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ)
    (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) (hsym : OutputSymmetric σ) :
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ (n : ℕ) (C : Finset (Fin n → Fin 2)), 2 ≤ C.card → ∀ ε : ℝ, 0 < ε →
        ∀ D : C → Matrix (Fin n → ι) (Fin n → ι) ℂ, (∀ c, (D c).PosSemidef) → ∑ c, D c = 1 →
          decoderSuccess σ C D ≤
            (2 : ℝ) ^ (-((n : ℝ) * (rate C - holevoUniform σ - 2 * ε))) +
              4 * Real.exp (-(ε ^ 2 * n / L ^ 2))) ∧
      (∀ Δ : ℝ, 0 < Δ → ∀ (n : ℕ) (C : Finset (Fin n → Fin 2)), 2 ≤ C.card →
        Δ ≤ rate C - holevoUniform σ →
        ∀ D : C → Matrix (Fin n → ι) (Fin n → ι) ℂ, (∀ c, (D c).PosSemidef) → ∑ c, D c = 1 →
          decoderSuccess σ C D ≤
            (2 : ℝ) ^ (-((n : ℝ) * Δ / 2)) + 4 * Real.exp (-(Δ ^ 2 * n / (16 * L ^ 2)))) := by sorry

end PrettyGoodCriterion

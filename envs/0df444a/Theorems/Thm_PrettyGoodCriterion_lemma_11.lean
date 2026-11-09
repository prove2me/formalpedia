-- Prove2me | Theorems.Thm_PrettyGoodCriterion_lemma_11
-- name    : PrettyGoodCriterion.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:35:56.134544+00:00
-- url     : https://prove2.me/theorems/57199b14-b58f-4dce-b437-8a241621ec1f
-- title:
--   Lemma 11 — the uniform prior maximizes the PGM bit error rate
-- statement:
--   Let $\sigma_0,\sigma_1$ be an output-symmetric pair of density matrices. For $\gamma\in[0,1]$ let $p_{e,\gamma}(\sigma_0,\sigma_1)$ be the PGM error of the binary ensemble $\mathcal E_\gamma=\{(1-\gamma,\sigma_0),(\gamma,\sigma_1)\}$. Then for every $\gamma\in[0,1]$
--   $$p_{e,\gamma}(\sigma_0,\sigma_1)\le p_{e,1/2}(\sigma_0,\sigma_1)=p_e(\sigma_0,\sigma_1).$$
--
--   In the proof of Theorem 17 the bit marginals of a code give a non-uniform prior $\gamma=\pi_i(1)$; this lemma removes the dependence on it.
--
--   Differences from the source:
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 11, p.18 (PDF 20); proof Appendix A.6, p.72 (PDF 74)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_OutputSymmetric

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Lemma 11 (Uniform prior maximizes the PGM bit error rate)**, Alrabiah–Guruswami,
arXiv:2608.09347 (held version), p.18 (PDF 20); proof in Appendix A.6, p.72 (PDF 74).

For an output-symmetric pair of density matrices `σ₀, σ₁` and every `γ ∈ [0, 1]`,
`p_{e,γ}(σ₀, σ₁) ⩽ p_{e,1/2}(σ₀, σ₁) = p_e(σ₀, σ₁)`, where `p_{e,γ}` is the PGM error of
`ℰ_γ = {(1 − γ, σ₀), (γ, σ₁)}`. -/
theorem lemma_11 {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ)
    (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) (hsym : OutputSymmetric σ) :
    (∀ γ ∈ Set.Icc (0 : ℝ) 1, pgmBitError γ σ ≤ pgmBitError (1 / 2) σ) ∧
      pgmBitError (1 / 2) σ = pgmBitErrorUniform σ := by sorry

end PrettyGoodCriterion

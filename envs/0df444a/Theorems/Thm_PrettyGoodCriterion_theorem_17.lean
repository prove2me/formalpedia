-- Prove2me | Theorems.Thm_PrettyGoodCriterion_theorem_17
-- name    : PrettyGoodCriterion.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:33.863081+00:00
-- url     : https://prove2.me/theorems/4edd7e71-80ef-4eca-9f52-190d1aa2b2df
-- title:
--   Theorem 17 — the PGM's expected Hamming distance is at most $n\,p_e(\sigma_0,\sigma_1)$
-- statement:
--   Let $b\mapsto\sigma_b$ be a binary-input output-symmetric cq channel with density outputs $\sigma_0,\sigma_1$, and $\mathcal C\subseteq\{0,1\}^n$ a code with $|\mathcal C|\ge2$. Let $c$ be a uniformly random codeword, $\sigma_c=\sigma_{c_1}\otimes\cdots\otimes\sigma_{c_n}$ its output state, and $\hat c$ the outcome of the PGM of $\mathcal C$ applied to $\sigma_c$. Then
--   $$\mathbb E\big[d(\hat c,c)\big]\le n\,p_e(\sigma_0,\sigma_1).$$
--
--   The PGM of the whole code thus makes on average no more bit errors than $n$ independent uses of the single-bit PGM. Combined with a minimum-distance guarantee it yields constant block-decoding success (Corollary 18).
--
--   Differences from the source:
--   - encoding: the PGM of 𝒞, i.e. of the uniform ensemble {(|𝒞|⁻¹, σ_c) : c ∈ 𝒞} with outcomes ĉ ∈ 𝒞 → the PGM (Definition 2.7) of the ensemble indexed by the subtype {c // c ∈ 𝒞} with prior |𝒞|⁻¹ and states HolevoCQ.wordState σ n c; reason: the same ensemble; the outcome set is the code itself
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Theorem 17, p.22 (PDF 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_OutputSymmetric
import Definitions.Def_PrettyGoodCriterion_codePGM

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Theorem 17 (PGM expected Hamming distance)**, Alrabiah–Guruswami, arXiv:2608.09347 (held
version), p.22 (PDF 24).

For a binary-input output-symmetric cq channel with density outputs `σ₀, σ₁`, a code
`𝒞 ⊆ {0,1}ⁿ` with `|𝒞| ⩾ 2` (standing assumption, p.14), a uniform codeword `c` and the outcome
`ĉ` of the PGM of `𝒞` applied to `σ_c = σ_{c₁} ⊗ ⋯ ⊗ σ_{cₙ}`:
`E[d(ĉ, c)] ⩽ n p_e(σ₀, σ₁)`. -/
theorem theorem_17 {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ)
    (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) (hsym : OutputSymmetric σ) {n : ℕ}
    (C : Finset (Fin n → Fin 2)) (hC : 2 ≤ C.card) :
    pgmExpectedDistance σ C ≤ n * pgmBitErrorUniform σ := by sorry

end PrettyGoodCriterion

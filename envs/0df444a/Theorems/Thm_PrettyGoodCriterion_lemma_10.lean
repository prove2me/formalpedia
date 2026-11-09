-- Prove2me | Theorems.Thm_PrettyGoodCriterion_lemma_10
-- name    : PrettyGoodCriterion.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:36:16.338572+00:00
-- url     : https://prove2.me/theorems/893ec390-4c37-425a-ac15-21df3d360e82
-- title:
--   Lemma 10 — PGM error is nondecreasing under quantum channels
-- statement:
--   Let $\mathcal E=\{(\pi_x,\sigma_x):x\in\mathcal X\}$ be a finite ensemble of density matrices ($\pi_x\ge0$, $\sum_x\pi_x=1$) and $\mathcal N:\mathbb C^{d_A\times d_A}\to\mathbb C^{d_B\times d_B}$ a completely positive trace-preserving linear map. Then applying $\mathcal N$ to every state cannot lower the PGM error:
--   $$p_e(\mathcal E)\le p_e\big(\{(\pi_x,\mathcal N(\sigma_x)):x\in\mathcal X\}\big).$$
--
--   This is the data-processing inequality for the PGM. In the proof of Theorem 17 it is applied to the partial trace onto one output qudit.
--
--   **Formalization Note** $\mathcal N$ is a $\mathbb C$-linear map `Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ`; complete positivity and trace preservation are the published `WildeQIT.EntBreaking.IsQuantumChannel`.
--
--   Differences from the source:
--   - encoding: complete positivity: 𝒩 ⊗ id_r is positive for every positive integer r (Definition 2.3) → WildeQIT.EntBreaking.IsQuantumChannel: id_r ⊗ 𝒩 on Fin r × A is positive for every r : ℕ, and Tr 𝒩(X) = Tr X; reason: the two orders of the tensor factors differ by a permutation of the index set, which preserves positive semidefiniteness, and r = 0 is vacuous
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 10, p.18 (PDF 20); proof Appendix A.2, p.67 (PDF 69)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Lemma 10 (PGM error is nondecreasing under quantum channels)**, Alrabiah–Guruswami,
arXiv:2608.09347 (held version), p.18 (PDF 20); proof in Appendix A.2, p.67 (PDF 69).

For a finite ensemble `ℰ = {(π_x, σ_x) : x ∈ 𝒳}` of density matrices (`π ⩾ 0`, `∑ π = 1`) and a
completely positive trace-preserving map `𝒩`,
`p_e(ℰ) ⩽ p_e({(π_x, 𝒩(σ_x)) : x ∈ 𝒳})`.

**Formalization Note.** `𝒩` is a `ℂ`-linear map `Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ` between
finite-dimensional matrix spaces, and "completely positive trace-preserving" is the published
`WildeQIT.EntBreaking.IsQuantumChannel` (complete positivity for every finite reference
`Fin r`, and `Tr 𝒩(X) = Tr X` for every `X`), which is Definition 2.3 of the paper. -/
theorem lemma_10 {X A B : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (p : X → ℝ) (σ : X → Matrix A A ℂ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) (hσ : ∀ x, QAlgorithms.IsDensityMatrix (σ x)) (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hN : WildeQIT.EntBreaking.IsQuantumChannel N) :
    pgmError p σ ≤ pgmError p (fun x => N (σ x)) := by sorry

end PrettyGoodCriterion

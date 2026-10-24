-- Prove2me | Theorems.Thm_WernerExt_TwoSided_azenhas_difference
-- name    : WernerExt.TwoSided.azenhas_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:35.933524+00:00
-- url     : https://prove2.me/theorems/91e7c593-fb6c-420b-93e0-319588a7056b
-- title:
--   SM Eq. (11), Supplemental Material p. 2 (Azenhas) — λ^AB − λ^A = sort{λ^AB_i − λ^A_i} lies in LR(λ^AB, λ^A) and is dominated by all of it
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$, $\lambda^{(A)}\vdash_dn_A$ and $\lambda^{(AB)}\vdash_dn_A+n_B$ with $\lambda^{(A)}_i\le\lambda^{(AB)}_i$ for all $i$. Let $LR(\lambda^{(AB)},\lambda^{(A)})$ be the set of $\lambda^{(B)}\vdash_dn_B$ such that $\lambda^{(AB)}$ appears in $\lambda^{(A)}\otimes\lambda^{(B)}$, and let
--   $$\lambda^{(AB)}-\lambda^{(A)}=\operatorname{sort}\{\lambda^{(AB)}_i-\lambda^{(A)}_i\}_{i=1}^d\vdash_dn_B$$
--   (sorted decreasingly). Then $\lambda^{(AB)}-\lambda^{(A)}\in LR(\lambda^{(AB)},\lambda^{(A)})$, and
--   $$\lambda^{(AB)}-\lambda^{(A)}\ \trianglelefteq\ \lambda^{(B)}\quad\text{for all }\lambda^{(B)}\in LR(\lambda^{(AB)},\lambda^{(A)}).$$
--
--   This result of Azenhas (1999) is the input for the minimum product diagram, Eq. (11).
--
--   **Formalization Note** A $d$-partition $\lambda\vdash_d n$ is represented by the published type `QAlgorithms.Schur.Partition d n` (Young diagrams with $n$ boxes and at most $d$ rows), read through its first $d$ row lengths; $c^{\nu}_{\lambda\mu}$ is the published polynomial Littlewood–Richardson coefficient `lrCoefficient d λ μ ν` (LR tableaux of shape $\nu/\lambda$ and content $\mu$).
--
--   Differences from the source:
--   - encoding: “λ^(AB) appears in λ^(A) ⊗ λ^(B)” for SU(d) irreps labelled by d-row partitions of fixed sizes → 0 < lrCoefficient d λ^A λ^B λ^AB (polynomial LR coefficient, λ^A inner shape, λ^B content); reason: at fixed box counts no two distinct partitions are SU(d)-equivalent (p. 2), so the SU(d) multiplicity is the polynomial LR coefficient
--   - encoding: the difference partition λ^(AB) − λ^(A) ⊢_d n_B → a Partition d n_B whose first d rows are sortDesc(λ^AB_i − λ^A_i), asserted to exist; reason: the sorted difference is a d-partition of n_B; stating its existence is part of the claim
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, Supplemental Material p. 2 (PDF 8), SM Eqs. (10)–(11)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- SM Eq. (11), SM p. 2 (Azenhas): for `λ^A ⊢_d nA` and `λ^AB ⊢_d nA + nB` with
`λ^A_i ≤ λ^AB_i` for all `i`, the difference partition `λ^AB − λ^A = sort{λ^AB_i − λ^A_i}`
belongs to `LR(λ^AB, λ^A)`, and it is dominated by every `λ^B ∈ LR(λ^AB, λ^A)`. -/
theorem azenhas_difference (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lAB : Partition d (nA + nB))
    (hsub : ∀ i : Fin d, lA.val.rowLen i ≤ lAB.val.rowLen i) :
    ∃ δ : Partition d nB,
      (fun i : Fin d => δ.val.rowLen i) =
          sortDesc (fun i : Fin d => lAB.val.rowLen i - lA.val.rowLen i) ∧
        0 < lrCoefficient d lA.val δ.val lAB.val ∧
        ∀ lB : Partition d nB, 0 < lrCoefficient d lA.val lB.val lAB.val →
          Dominates (fun i : Fin d => lB.val.rowLen i) (fun i : Fin d => δ.val.rowLen i) := by sorry

end WernerExt.TwoSided

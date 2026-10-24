-- Prove2me | Theorems.Thm_WernerExt_TwoSided_lr_dual_symmetry
-- name    : WernerExt.TwoSided.lr_dual_symmetry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:38.748978+00:00
-- url     : https://prove2.me/theorems/2cf7b827-e3c2-40e5-a22a-ac16e6bcbf3e
-- title:
--   SM Eq. (13), Supplemental Material p. 2 — m(λ^A, λ^B, λ^AB) = m(λ^A, λ̄^AB, λ̄^B): exchanging λ^AB and λ^B and dualizing both preserves the multiplicity
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$, $\lambda^{(A)}\vdash_dn_A$, $\lambda^{(B)}\vdash_dn_B$, $\lambda^{(AB)}\vdash_dn_A+n_B$, and let $M$ be an integer with $M\ge\lambda^{(B)}_1$ and $M\ge\lambda^{(AB)}_1$. Write $\bar\lambda_i=M-\lambda_{d-i+1}$ for the $M$-dual. Then the multiplicity of $\lambda^{(AB)}$ in $\lambda^{(A)}\otimes\lambda^{(B)}$ equals the multiplicity of $\overline{\lambda^{(B)}}$ in $\lambda^{(A)}\otimes\overline{\lambda^{(AB)}}$:
--   $$m\big(\lambda^{(A)},\lambda^{(B)},\lambda^{(AB)}\big)=m\big(\lambda^{(A)},\overline{\lambda^{(AB)}},\overline{\lambda^{(B)}}\big).$$
--
--   This dual symmetry turns the Azenhas result into the minimum product diagram.
--
--   **Formalization Note** A $d$-partition $\lambda\vdash_d n$ is represented by the published type `QAlgorithms.Schur.Partition d n` (Young diagrams with $n$ boxes and at most $d$ rows), read through its first $d$ row lengths; $c^{\nu}_{\lambda\mu}$ is the published polynomial Littlewood–Richardson coefficient `lrCoefficient d λ μ ν` (LR tableaux of shape $\nu/\lambda$ and content $\mu$). Both duals are taken with the same $M$, so that $|\lambda^{(A)}|+|\overline{\lambda^{(AB)}}|=|\overline{\lambda^{(B)}}|$; the duals are any `Partition`s whose first $d$ rows are the $M$-dual rows (they exist and are unique).
--
--   Differences from the source:
--   - encoding: the SU(d) multiplicity m(·,·,·) of irreps labelled up to columns of height d → the polynomial LR coefficient on d-row partitions, with both duals taken for one common M ≥ λ^B_1, λ^AB_1; reason: with a common M the box counts match, and at fixed box counts the SU(d) multiplicity is the polynomial LR coefficient (p. 2)
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, Supplemental Material p. 2 (PDF 8), SM Eqs. (12)–(13); duals p. 2

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- SM Eq. (13), SM p. 2: the multiplicity `m(λ^A, λ^B, λ^AB)` of `λ^AB` in `λ^A ⊗ λ^B` is
invariant under exchanging `λ^AB` and `λ^B` and replacing both by their `M`-duals:
`m(λ^A, λ^B, λ^AB) = m(λ^A, \overline{λ^AB}, \overline{λ^B})`, for a common `M` at least the
first rows of `λ^B` and `λ^AB`. -/
theorem lr_dual_symmetry (d nA nB M : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lB : Partition d nB) (lAB : Partition d (nA + nB))
    (hM : ∀ i : Fin d, lB.val.rowLen i ≤ M ∧ lAB.val.rowLen i ≤ M)
    {m k : ℕ} (dAB : Partition d m) (dB : Partition d k)
    (hdAB : (fun i : Fin d => dAB.val.rowLen i) = mDual M (fun i : Fin d => lAB.val.rowLen i))
    (hdB : (fun i : Fin d => dB.val.rowLen i) = mDual M (fun i : Fin d => lB.val.rowLen i)) :
    lrCoefficient d lA.val lB.val lAB.val = lrCoefficient d lA.val dAB.val dB.val := by sorry

end WernerExt.TwoSided

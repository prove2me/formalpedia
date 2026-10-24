-- Prove2me | Theorems.Thm_WernerExt_TwoSided_min_product_diagram
-- name    : WernerExt.TwoSided.min_product_diagram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:49.942689+00:00
-- url     : https://prove2.me/theorems/1a81cfcd-bcef-4846-b20e-ed518013abe6
-- title:
--   Eq. (11), p. 3 (= SM Eq. (16)) — sort{λ^A_i + λ^B_{d−i+1}} is the dominance minimum of the irreps in λ^A ⊗ λ^B
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$, $\lambda^{(A)}\vdash_dn_A$ and $\lambda^{(B)}\vdash_dn_B$. The irrep decomposition of $\lambda^{(A)}\otimes\lambda^{(B)}$ has a minimum with respect to dominance order,
--   $$\hat\lambda^{(AB)}(\lambda^{(A)},\lambda^{(B)})=\operatorname{sort}\{\lambda^{(A)}_i+\lambda^{(B)}_{d-i+1}\}_{i=1}^d:$$
--
--   1. $\hat\lambda^{(AB)}$ appears in $\lambda^{(A)}\otimes\lambda^{(B)}$;
--   2. every $\lambda^{(AB)}\vdash_dn_A+n_B$ appearing in $\lambda^{(A)}\otimes\lambda^{(B)}$ satisfies $\lambda^{(AB)}\trianglerighteq\hat\lambda^{(AB)}$.
--
--   The rows of $\lambda^{(B)}$ are turned upside down, attached to those of $\lambda^{(A)}$, and the result sorted decreasingly. This is the diagram that enters $E^W$ in Eq. (12).
--
--   **Formalization Note** A $d$-partition $\lambda\vdash_d n$ is represented by the published type `QAlgorithms.Schur.Partition d n` (Young diagrams with $n$ boxes and at most $d$ rows), read through its first $d$ row lengths; $c^{\nu}_{\lambda\mu}$ is the published polynomial Littlewood–Richardson coefficient `lrCoefficient d λ μ ν` (LR tableaux of shape $\nu/\lambda$ and content $\mu$).
--
--   Differences from the source:
--   - encoding: “λ^(AB) appears in λ^(A) ⊗ λ^(B)” for SU(d) irreps labelled by d-row partitions of fixed sizes → 0 < lrCoefficient d λ^A λ^B λ^AB (polynomial LR coefficient, λ^A inner shape, λ^B content); reason: at fixed box counts no two distinct partitions are SU(d)-equivalent (p. 2), so the SU(d) multiplicity is the polynomial LR coefficient
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 3, Eq. (11); Supplemental Material p. 3 (PDF 9), SM Eqs. (15)–(16)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- Eq. (11), p. 3 (= SM Eq. (16)): the irrep decomposition of `λ^A ⊗ λ^B` has a minimum in
dominance order, `λ̂^(AB)(λ^A, λ^B) = sort{λ^A_i + λ^B_{d−i+1}}_{i=1}^d`: (a) it appears in
`λ^A ⊗ λ^B`, and (b) it is dominated by every `λ^AB` that appears. -/
theorem min_product_diagram (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lB : Partition d nB) :
    (∃ lAB : Partition d (nA + nB),
        (fun i : Fin d => lAB.val.rowLen i) =
            minProduct (fun i : Fin d => lA.val.rowLen i) (fun i : Fin d => lB.val.rowLen i) ∧
          0 < lrCoefficient d lA.val lB.val lAB.val) ∧
      ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
        Dominates (fun i : Fin d => lAB.val.rowLen i)
          (minProduct (fun i : Fin d => lA.val.rowLen i) (fun i : Fin d => lB.val.rowLen i)) := by sorry

end WernerExt.TwoSided

-- Prove2me | Theorems.Thm_WernerExt_TwoSided_min_casimir
-- name    : WernerExt.TwoSided.min_casimir
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:41.657221+00:00
-- url     : https://prove2.me/theorems/c69dc68b-abe1-4ff7-be70-5806efa3d9e2
-- title:
--   p. 3 — a dominance-minimal irrep of λ^A ⊗ λ^B has the smallest Casimir eigenvalue among the product diagrams
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$, $\lambda^{(A)}\vdash_dn_A$, $\lambda^{(B)}\vdash_dn_B$. If $\lambda^{0}\vdash_dn_A+n_B$ appears in $\lambda^{(A)}\otimes\lambda^{(B)}$ and is dominated by every irrep appearing there (a minimum with respect to dominance order), then
--   $$c(\lambda^{0})\le c(\lambda^{(AB)})\quad\text{for every }\lambda^{(AB)}\text{ appearing in }\lambda^{(A)}\otimes\lambda^{(B)}.$$
--
--   Combined with Eq. (11), this identifies the lowest eigenvalue of $C_{AB}$ on the $(\lambda^{(A)},\lambda^{(B)})$ sector, which gives $E^W$.
--
--   **Formalization Note** A $d$-partition $\lambda\vdash_d n$ is represented by the published type `QAlgorithms.Schur.Partition d n` (Young diagrams with $n$ boxes and at most $d$ rows), read through its first $d$ row lengths; $c^{\nu}_{\lambda\mu}$ is the published polynomial Littlewood–Richardson coefficient `lrCoefficient d λ μ ν` (LR tableaux of shape $\nu/\lambda$ and content $\mu$).
--
--   Differences from the source:
--   - encoding: “λ^(AB) appears in λ^(A) ⊗ λ^(B)” for SU(d) irreps labelled by d-row partitions of fixed sizes → 0 < lrCoefficient d λ^A λ^B λ^AB (polynomial LR coefficient, λ^A inner shape, λ^B content); reason: at fixed box counts no two distinct partitions are SU(d)-equivalent (p. 2), so the SU(d) multiplicity is the polynomial LR coefficient
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 3, 'Thus, if the set of irreps that appear in the irrep decomposition of λ^(A) ⊗ λ^(B) has a minimum …'

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- p. 3: if the set of irreps appearing in `λ^A ⊗ λ^B` has a minimum `λ^0` in dominance
order, then `λ^0` has the smallest quadratic Casimir eigenvalue among the product diagrams. -/
theorem min_casimir (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lB : Partition d nB) (l0 : Partition d (nA + nB))
    (h0 : 0 < lrCoefficient d lA.val lB.val l0.val)
    (hmin : ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      Dominates (fun i : Fin d => lAB.val.rowLen i) (fun i : Fin d => l0.val.rowLen i)) :
    ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      casimirValue (fun i : Fin d => l0.val.rowLen i) ≤
        casimirValue (fun i : Fin d => lAB.val.rowLen i) := by sorry

end WernerExt.TwoSided

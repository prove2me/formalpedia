-- Prove2me | Theorems.Thm_WernerExt_TwoSided_hamW_spectrum
-- name    : WernerExt.TwoSided.hamW_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:30.763787+00:00
-- url     : https://prove2.me/theorems/3f4973eb-480d-425b-88b5-9b31bb531a38
-- title:
--   p. 3 — the eigenvalues of H_W are [c(λ^AB) − c(λ^A) − c(λ^B)]/(2 n_A n_B) + 1/d over the LR-compatible triples
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$. A real number $e$ is an eigenvalue of $H^W$ if and only if there are $\lambda^{(A)}\vdash_dn_A$, $\lambda^{(B)}\vdash_dn_B$ and $\lambda^{(AB)}\vdash_dn_A+n_B$ such that $\lambda^{(AB)}$ appears in the decomposition of $\lambda^{(A)}\otimes\lambda^{(B)}$ (the Littlewood–Richardson coefficient $c^{\lambda^{(AB)}}_{\lambda^{(A)}\lambda^{(B)}}$ is positive) and
--   $$e=\frac{1}{2n_An_B}\left[c(\lambda^{(AB)})-c(\lambda^{(A)})-c(\lambda^{(B)})\right]+\frac1d.$$
--
--   This labels the spectrum of $H^W$ by compatible triples of Young diagrams, reducing the ground state problem to a combinatorial minimization.
--
--   **Formalization Note** A $d$-partition $\lambda\vdash_d n$ is represented by the published type `QAlgorithms.Schur.Partition d n` (Young diagrams with $n$ boxes and at most $d$ rows), read through its first $d$ row lengths; $c^{\nu}_{\lambda\mu}$ is the published polynomial Littlewood–Richardson coefficient `lrCoefficient d λ μ ν` (LR tableaux of shape $\nu/\lambda$ and content $\mu$).
--
--   Differences from the source:
--   - reading: the eigenvalues of H_W are labelled by the compatible triples (λ^(A), λ^(B), λ^(AB)) → the set of eigenvalues equals the set of values [c(λ^AB) − c(λ^A) − c(λ^B)]/(2 n_A n_B) + 1/d over compatible triples; reason: the value of a triple is Eq. (5) with Eq. (9), as the paper uses it in Eq. (12)
--   - encoding: “λ^(AB) appears in λ^(A) ⊗ λ^(B)” for SU(d) irreps labelled by d-row partitions of fixed sizes → 0 < lrCoefficient d λ^A λ^B λ^AB (polynomial LR coefficient, λ^A inner shape, λ^B content); reason: at fixed box counts no two distinct partitions are SU(d)-equivalent (p. 2), so the SU(d) multiplicity is the polynomial LR coefficient
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 3, 'Since the Casimirs that appear in H^W and H^I commute …'; Eqs. (5), (9)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- p. 3: the eigenvalues of `H_W` are labelled by the triples `(λ^A, λ^B, λ^AB)` of
`d`-partitions of `nA`, `nB`, `nA + nB` for which `λ^AB` appears in `λ^A ⊗ λ^B`
(Littlewood–Richardson coefficient `c^{λ^AB}_{λ^A λ^B} > 0`); the eigenvalue of a triple is
`[c(λ^AB) − c(λ^A) − c(λ^B)]/(2 nA nB) + 1/d`. -/
theorem hamW_spectrum (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB) (e : ℝ) :
    IsEigenvalue (hamW d nA nB) e ↔
      ∃ (lA : Partition d nA) (lB : Partition d nB) (lAB : Partition d (nA + nB)),
        0 < lrCoefficient d lA.val lB.val lAB.val ∧
          e = (casimirValue (fun i : Fin d => lAB.val.rowLen i) -
                casimirValue (fun i : Fin d => lA.val.rowLen i) -
                casimirValue (fun i : Fin d => lB.val.rowLen i)) /
              (2 * (nA : ℝ) * (nB : ℝ)) + 1 / (d : ℝ) := by sorry

end WernerExt.TwoSided

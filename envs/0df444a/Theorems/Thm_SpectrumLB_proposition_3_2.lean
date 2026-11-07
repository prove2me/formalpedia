-- Prove2me | Theorems.Thm_SpectrumLB_proposition_3_2
-- name    : SpectrumLB.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:38.191359+00:00
-- url     : https://prove2.me/theorems/cbe76c19-9e76-454f-872c-f7ba86907d56
-- title:
--   Proposition 3.2 — $\mathbf E[\Pi^{\otimes n}]=\prod_t(r+J_t)/\prod_t(d+J_t)$ for a Haar-random rank-$r$ projection
-- statement:
--   Let $\Pi$ be a Haar-random rank-$r$ projection on $\mathbb C^d$, $r\le d$, and let $J_1,\dots,J_n$ be the Jucys–Murphy elements acting on $(\mathbb C^d)^{\otimes n}$. Then
--
--   1. the $J_t$ commute pairwise;
--   2. each operator $d+J_t$ is invertible;
--   3. the $n$-fold tensor moment of $\Pi$ is
--
--   $$
--   \mathbf E\big[\Pi^{\otimes n}\big]=\frac{(r+J_1)(r+J_2)\cdots(r+J_n)}{(d+J_1)(d+J_2)\cdots(d+J_n)} .
--   $$
--
--   This is the noncommutative analogue of the inclusion probability $r(r-1)\cdots/(d(d-1)\cdots)$ of a random subset, and the exact moment formula from which all moments of the hard ensembles are computed.
--
--   Differences from the source:
--   - encoding: Haar-random rank-r projection → U·diag(1,…,1,0,…,0)·U† with U Haar distributed on U(d); reason: Eq. (3.1); the same law
--   - encoding: ratio of commuting operators → (∏_t (r·1 + J_t)) · (∏_t (d·1 + J_t))⁻¹, products over t = 1, …, n in order, with clauses 1–2 stated explicitly; reason: the statement's own sentence "the ratio of operators makes sense since the Jucys–Murphy elements commute and each denominator factor (d + J_t) is invertible"
--   - encoding: E of a random matrix → entrywise expectation; reason: same matrix
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 3.2, Eq. (3.3), p. 13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_SpectrumLB_jm
import Definitions.Def_SpectrumLB_haarProj
import Definitions.Def_WildeQIT_Covering_expectation

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Proposition 3.2 (tensor moments of a Haar-random projection).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 3.2, Eq. (3.3), p. 13: "For a Haar-random rank-r projection Π on C^d,
E[Π^{⊗n}] = (r + J_1)(r + J_2) ⋯ (r + J_n) / ((d + J_1)(d + J_2) ⋯ (d + J_n)). Here, the ratio of operators
makes sense since the Jucys–Murphy elements commute and each denominator factor (d + J_t) is invertible."

For `r ≤ d`: (a) the `J_t` pairwise commute; (b) each `d + J_t` is invertible; (c) the entrywise mean of
`(U R U†)^{⊗n}` over Haar `U` equals `∏_t (r + J_t) · (∏_t (d + J_t))⁻¹`.

**Formalization Note.** `r + J_t` is `r · 1 + J_t` on `(ℂ^d)^{⊗n}`; products run over `t = 0, …, n−1`
(0-based). Clauses (a), (b) are the sentence "Here, …" of the statement. `r ≤ d` is "rank-r projection on
C^d". -/
theorem proposition_3_2 (d r n : ℕ) (hr : r ≤ d) :
    (∀ s t : Fin n, Commute (jm d s) (jm d t)) ∧
    (∀ t : Fin n,
      IsUnit ((d : ℂ) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) + jm d t)) ∧
    WildeQIT.Covering.expectation (QAlgorithms.Schur.unitaryHaar d) (fun U => QAlgorithms.piKron n (haarProj r U)) =
      (List.ofFn fun t : Fin n =>
          (r : ℂ) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) + jm d t).prod *
      (List.ofFn fun t : Fin n =>
          (d : ℂ) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) + jm d t).prod⁻¹ := by sorry

end SpectrumLB

-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_41_centered
-- name    : SpencerEight.lemma_8_41_centered
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:38.901938+00:00
-- url     : https://prove2.me/theorems/c3874ea2-b188-4572-8067-77dc8280739e
-- title:
--   Lemma 8.41, centered-row clause — the rows of Definition 8.39
-- statement:
--   This item states the part of Lemma 8.41 about the centered rows; the first half of that lemma, on general rows from Section 8.10, is not stated here.
--
--   Fix a row $j\in\{0,\dots,6\}$ of Definition 8.39, with $(\eta,e^\circ,\beta):=(\eta_j,e^\circ_j,\beta_j)$. For $0<\rho\le1$, symmetric contractions $B_i\in\mathbb R^{n\times n}$ with $\operatorname{tr}[B_i^2]\le\rho n$, every $w>0$, and every nonempty subfamily $S$ of size $m\le wn$,
--   $$\gamma_m\Bigl[\bigl\|\sum_{i\in S}\xi_iB_i\bigr\|\le\sqrt{wn/\eta_j}\Bigr]\ge\exp[-m(\rho e^\circ_j/w+\beta_j/2)].$$
--   A retention $q\in(0,1)$ is valid for lossless coding whenever
--   $$\rho e^\circ_j+\beta_jw/2<w(q^2/2+q^4/12),\tag{121}$$
--   and the partial-signing increment is at most $s_\star^{-1}\sqrt{w/\eta_j}\sqrt n$: under (121) there is $y\in\{-1,0,1\}^S$ with fewer than $qm$ zero coordinates and $\|\sum_{i\in S}y_iB_i\|\le s_\star^{-1}\sqrt{w/\eta_j}\sqrt n$.
--
--   These rows close the signing schedule after the eleven prefix phases.
--
--   Differences from the source:
--   - reading: Fix a row obtained from the radial bounds of Section 8.10 … Then … In particular, Lemma 8.40 verifies these hypotheses for every centered row j → the conclusion at the seven printed rows only, under the marked title; reason: the page's own "in particular" sentence is the statement; the general half quantifies over a proof construction and is not stated in this item (recorded in the mission notes)
--   - reading: A retention q is valid for lossless coding; the partial-signing increment is at most s⋆⁻¹√(w/η_j)√n → under (121) there is y ∈ {−1, 0, 1}^S with fewer than qm zeros and ‖Σ y_iB_i‖ ≤ s⋆⁻¹√(w/η_j)√n; reason: the proof states this as the coding consequence via Lemma 8.3
--   - encoding: a nonempty subfamily S of size m, Gaussian on ℝ^m → a nonempty Finset S of a finite index type, m = |S|, Gaussian on S → ℝ; reason: the same object
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.41, p.103 (PDF p.103); Definition 8.39, p.102 (PDF p.102)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_sStar
import Definitions.Def_SpencerEight_etaRow
import Definitions.Def_SpencerEight_eCircRow
import Definitions.Def_SpencerEight_betaRow
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.41, centered-row clause (Trace-sensitive row interface at the rows of Definition 8.39), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.103 (PDF p.103). **This item states only part of Lemma 8.41:** the measure bound at the seven centered rows, with their printed `(η_j, e°_j, β_j)`, plus the two sentences on retention under Eq. (121) and on the partial-signing increment. The first half of the lemma, which quantifies over rows obtained from the radial bounds of Section 8.10, is a hypothesis on a proof construction and is not stated.

**Formalization Note** A subfamily is a nonempty `S`, with the Gaussian on `ℝ^S`, `m = |S|`. The coding consequence reads: for `q ∈ (0, 1)` with Eq. (121), there is `y ∈ {−1, 0, 1}^S` with fewer than `qm` zeros and `‖∑ yᵢBᵢ‖ ≤ s⋆⁻¹ √(w/η_j) √n`. -/
theorem lemma_8_41_centered (j : Fin 7) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {n : ℕ}
    {ι : Type*} [Fintype ι] (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, IsSymmContraction (B i)) (htr : ∀ i, (B i ^ 2).trace ≤ ρ * n) {w : ℝ}
    (hw : 0 < w) (S : Finset ι) (hS : S.Nonempty) (hm : (S.card : ℝ) ≤ w * n) :
    ENNReal.ofReal (Real.exp (-((S.card : ℝ) * (ρ * eCircRow j / w + betaRow j / 2)))) ≤
      gammaM S {ξ | ‖∑ i : S, ξ i • B i‖ ≤ Real.sqrt (w * n / etaRow j)} ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      ρ * eCircRow j + betaRow j * w / 2 < w * (q ^ 2 / 2 + q ^ 4 / 12) →
      ∃ y : S → ℝ, (∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) ∧
        ((Finset.univ.filter fun i => y i = 0).card : ℝ) < q * S.card ∧
        ‖∑ i : S, y i • B i‖ ≤ sStar⁻¹ * Real.sqrt (w / etaRow j) * Real.sqrt n) := by sorry

end SpencerEight

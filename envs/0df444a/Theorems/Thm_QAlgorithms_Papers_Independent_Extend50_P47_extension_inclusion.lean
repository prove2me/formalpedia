-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_extension_inclusion
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.extension_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:16:08.290667+00:00
-- url     : https://prove2.me/theorems/2b6d4f5c-fa47-4047-84a5-ee32b3ac6949
-- title:
--   Bose symmetric extendibility implies symmetric extendibility
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   Every G-BSE state is G-symmetric extendible for the same R,S,U; the converse fails for a finite-dimensional ordinary sign representation.
--
--   $$
--   \mathrm{BSE}_G\subseteq\mathrm{SymExt}_G,\qquad\mathrm{SymExt}_G\not\subseteq\mathrm{BSE}_G\text{ in general}.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 4, Bose symmetric extendibility implies symmetric extendibility

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF p.4: Bose extendibility implies invariant extendibility. The reverse
fails, witnessed by the one-dimensional sign representation of the order-two group. -/
theorem extension_inclusion [Nonempty S] [Nonempty R] (U : G →* Matrix.unitaryGroup (R × S) ℂ) :
    (∀ rho, BSE (fun g => (U g : Mat (R × S))) rho →
      SE (fun g => (U g : Mat (R × S))) rho) ∧
    (∃ (V : Multiplicative (ZMod 2) →* Matrix.unitaryGroup (Unit × Unit) ℂ)
      (rho : Mat Unit), SE (fun g => (V g : Mat (Unit × Unit))) rho ∧
        ¬ BSE (fun g => (V g : Mat (Unit × Unit))) rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end

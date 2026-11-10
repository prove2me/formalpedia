-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_adapted_contraction
-- name    : SivanLPTensor.Recovery.adapted_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:33:18.260213+00:00
-- url     : https://prove2.me/theorems/df19d9d3-49d0-4019-8487-a9e3704ffd8e
-- title:
--   Corollary 3.6 — Contraction in an L-adapted basis
-- statement:
--   Under the LP setup of Lemma 3.5, choose a generic section $V$, arbitrary complements $\mathcal F_i=\mathcal L_i\oplus\mathcal R_i$, and arbitrary basis matrices $B_i,C_i$ of those section and complement spaces. For every full-rank frame $P$ in $\mathcal L^\perp$, there is a unique invertible $M_i$ with
--   $$F_i=[B_i,C_i]M_i,\qquad\Omega_P(T_i)=\det(M_i)\det(PC_i)\operatorname{Alt}(B_i)\in\bigwedge^2\mathcal L_i.$$
--   If $\det(PC_i)\ne0$, the component image is $\mathcal L_i$. If these determinants are nonzero for all $i$, then $\operatorname{Im}\Omega_P(T)=\bigoplus_i\mathcal L_i=\mathcal L$.
--   This retains the LP standing setup and both conditional image assertions; it relates the computed contraction to arbitrary adapted bases without assuming its image beforehand.
--
--   Differences from the source:
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
--   - encoding: generic Grassmannian points → nonzero-polynomial exceptional sets in full-rank frame coordinates; reason: frames represent exactly the source subspaces; all quantified basis choices are retained
--   - encoding: the section spaces and complements are as in Lemma 3.5 → all generic-section dimension, directness and separation conclusions are conjoined explicitly; reason: prevents conditional basis quantification from becoming vacuous when the section dimensions are wrong
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Corollary 3.6, printed p. 11 / PDF p. 13

import Definitions.Def_SivanLPTensor_Recovery_geometryModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem adapted_contraction {d r : ℕ} {n : Fin (d + 2) → ℕ}
    (hd : 1 ≤ d) (hn : ∀ j, 0 < n j) (hr : 0 < r)
    (a : Factors n r) (ha : NonzeroFactors a) (hLP : LP a) :
    GenericFrame (fun Vframe : Matrix (Fin d) (BlockIndex n) ℝ =>
      SectionGeometry (factorSpace a) d Vframe ∧
      (      ∀ R : Fin r → Submodule ℝ (Ambient n),
        (∀ i, Disjoint (sectionFamily (factorSpace a) Vframe i) (R i) ∧
          sectionFamily (factorSpace a) Vframe i ⊔ R i = factorSpace a i) →
      ∀ (B : Fin r → Matrix (BlockIndex n) (Fin 2) ℝ)
        (C : Fin r → Matrix (BlockIndex n) (Fin d) ℝ),
        (∀ i, IsBasisFrame (B i) (sectionFamily (factorSpace a) Vframe i)) →
        (∀ i, IsBasisFrame (C i) (R i)) →
      ∀ P : Matrix (Fin d) (BlockIndex n) ℝ, FullRows P →
        (∀ t, P t ∈ annihilator (totalSection (factorSpace a) Vframe)) →
        (∀ i, ∃! M : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ,
          Matrix.det M ≠ 0 ∧ factorFrame a i = concatenate (B i) (C i) * M ∧
          omega (pureTensor (fun j => a j i)) P =
            (Matrix.det M * Matrix.det (P * C i)) •
              altTwo (fun x => B i x 0) (fun x => B i x 1) ∧
          omega (pureTensor (fun j => a j i)) P ∈
            alternatingSquare (sectionFamily (factorSpace a) Vframe i) ∧
          (Matrix.det (P * C i) ≠ 0 →
            image (omega (pureTensor (fun j => a j i)) P) =
              sectionFamily (factorSpace a) Vframe i)) ∧
        ((∀ i, Matrix.det (P * C i) ≠ 0) →
          image (omega (synthesis a) P) = totalSection (factorSpace a) Vframe ∧
          ∀ (v : (i : Fin r) → sectionFamily (factorSpace a) Vframe i),
            (∑ i, (v i : Ambient n)) = 0 → ∀ i, v i = 0))) := by sorry

end SivanLPTensor.Recovery

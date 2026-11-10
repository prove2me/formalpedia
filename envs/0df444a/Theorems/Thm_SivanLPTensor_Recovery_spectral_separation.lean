-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_spectral_separation
-- name    : SivanLPTensor.Recovery.spectral_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:33:03.024631+00:00
-- url     : https://prove2.me/theorems/7d905cb2-8c16-4193-98c5-9d51ef17c263
-- title:
--   Lemma 3.7 — Spectral separation
-- statement:
--   For an LP-compliant nonzero real decomposition, let $d=m-2$ and choose generic $P\in\operatorname{Gr}(d,X^*)$. Put $V=\ker P$, choose any complements as in Lemma 3.5 and fix any basis matrices $C_i$ for them. For generic $Q\in\operatorname{Gr}(d,\mathcal L^\perp)$,
--   $$\det(PC_i)\ne0,\qquad\det(QC_i)\ne0,\qquad\rho_i=\frac{\det(QC_i)}{\det(PC_i)}\quad\text{are pairwise distinct}.$$
--   Genericity for $Q$ is conditional on the preceding section and complements; it is not an independent draw over the whole ambient space. This supplies all nonvanishing denominators and the exact eigenvalue separation used by Algorithm 1.
--
--   Differences from the source:
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
--   - encoding: generic Grassmannian points → nonzero-polynomial exceptional sets in full-rank frame coordinates; reason: frames represent exactly the source subspaces; all quantified basis choices are retained
--   - encoding: the section spaces and complements are as in Lemma 3.5 → all generic-section dimension, directness and separation conclusions are conjoined explicitly; reason: prevents conditional basis quantification from becoming vacuous when the section dimensions are wrong
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Lemma 3.7, printed p. 11 / PDF p. 13; proof printed p. 12 / PDF p. 14

import Definitions.Def_SivanLPTensor_Recovery_geometryModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem spectral_separation {d r : ℕ} {n : Fin (d + 2) → ℕ}
    (hd : 1 ≤ d) (hn : ∀ j, 0 < n j) (hr : 0 < r)
    (a : Factors n r) (ha : NonzeroFactors a) (hLP : LP a) :
    GenericFrame (fun P : Matrix (Fin d) (BlockIndex n) ℝ =>
      SectionGeometry (factorSpace a) d P ∧
      (      ∀ R : Fin r → Submodule ℝ (Ambient n),
        (∀ i, Disjoint (sectionFamily (factorSpace a) P i) (R i) ∧
          sectionFamily (factorSpace a) P i ⊔ R i = factorSpace a i) →
      ∀ B : Fin r → Matrix (BlockIndex n) (Fin d) ℝ,
        (∀ i, IsBasisFrame (B i) (R i)) →
        GenericIn (annihilator (totalSection (factorSpace a) P))
          (fun Q : Matrix (Fin d) (BlockIndex n) ℝ =>
            (∀ i, Matrix.det (P * B i) ≠ 0 ∧ Matrix.det (Q * B i) ≠ 0) ∧
            Function.Injective (fun i => Matrix.det (Q * B i) / Matrix.det (P * B i))))) := by sorry

end SivanLPTensor.Recovery

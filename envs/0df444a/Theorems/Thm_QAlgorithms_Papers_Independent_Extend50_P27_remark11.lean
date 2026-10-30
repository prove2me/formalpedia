-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_remark11
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.remark11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:41:01.674362+00:00
-- url     : https://prove2.me/theorems/6e438dfb-2095-4b1f-bcdb-bfbc994330aa
-- title:
--   Remark 11: PSD of all physical principal restrictions
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   For every $N,d\ge1$,
--
--   $$M_N^{(d)}\succeq0.$$
--
--   Thus every physical height restriction is positive semidefinite.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 12, Remark 11: PSD of all physical principal restrictions

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Remark 11: every physical principal restriction is PSD (PDF p.12). -/
theorem remark11 {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (teleportMatrix d N).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end

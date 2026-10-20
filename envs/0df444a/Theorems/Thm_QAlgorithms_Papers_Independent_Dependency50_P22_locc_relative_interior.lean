-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_locc_relative_interior
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.locc_relative_interior
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:19:58.811516+00:00
-- url     : https://prove2.me/theorems/5d52d1a5-e1c5-45d6-b247-5261416b6a05
-- title:
--   Nonempty relative interior of finite-outcome LOCC
-- statement:
--   Fix positive integers $N,m$ and positive local dimensions $d_1,\ldots,d_N$. Let $\mathrm{CP}[m]$ be the space of trace-preserving instruments with $m$ labeled CP branches on the fixed multipartite system. In its relative finite-dimensional topology,
--   $$
--   \operatorname{int}_{\mathrm{CP}[m]}\bigl(\mathrm{LOCC}[m]\bigr)\ne\varnothing.
--   $$
--   This is an interior assertion within the instrument space, so trace preservation is retained. It expresses stability of some LOCC implementations under sufficiently small physically valid perturbations.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 8, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF pp.8–10, Theorem 1: interior relative to the space of trace-preserving instruments. -/
theorem locc_relative_interior {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k) :
    (interior {J : {J : Fin m → Superop (Config d) (Config d) // IsInstrument J} |
      InLOCC d J.val}).Nonempty := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

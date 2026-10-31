-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_conjugation_no_go
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.conjugation_no_go
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:06:15.160663+00:00
-- url     : https://prove2.me/theorems/31768464-ef6f-480b-a860-4c81c59e0d4a
-- title:
--   Universal conjugation no-go below d−1 uses
-- statement:
--   Let $d\ge1$ and $0\le k<d-1$. Suppose a fixed general physical $k$-slot instrument implements the channel of the entrywise conjugate $U^*$ exactly on success for every $U\in U(d)$, with one constant coefficient $p\in[0,1]$. Then
--
--   $$p=0.$$
--
--   The general class includes indefinite-order processes and retains the failure branch. The basis defining complex conjugation is fixed. This gives a necessary query threshold for any nonzero universal conjugation probability.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 10, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.10–12, Theorem 1: even a general indefinite-order process cannot
conjugate universally with nonzero constant success if k<d-1. -/
theorem conjugation_no_go {d k : ℕ} (hd : 0 < d) (hk : k < d-1)
    (p : ℝ) (hp : Attainable .general d k (targetChoi .conjugate) p) :
    p = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end

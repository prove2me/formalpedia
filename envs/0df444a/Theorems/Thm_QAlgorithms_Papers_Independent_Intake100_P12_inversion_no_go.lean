-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_inversion_no_go
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.inversion_no_go
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:12:06.492362+00:00
-- url     : https://prove2.me/theorems/1c265cf9-3afb-4fa2-aa3e-7ca61eaea8f8
-- title:
--   Universal inversion no-go below d−1 uses
-- statement:
--   Let $d\ge1$ and $0\le k<d-1$. If a fixed general physical $k$-slot instrument implements the inverse channel of every unknown $U\in U(d)$ exactly on success with a constant probability $p\in[0,1]$, then
--
--   $$p=0.$$
--
--   This includes indefinite causal order, and the jointly normalized failure branch remains part of the instrument. It gives the inversion query threshold for nonzero universal success.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 18, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.18, Theorem 3: universal exact inversion with k<d-1 has zero constant
success, including general processes. The proof's reference to Lemma 1 means
Theorem 1, as its reduction is to the conjugation no-go. -/
theorem inversion_no_go {d k : ℕ} (hd : 0 < d) (hk : k < d-1)
    (p : ℝ) (hp : Attainable .general d k (targetChoi .inverse) p) :
    p = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_bounded_fine_branches
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.bounded_fine_branches
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:22:32.073863+00:00
-- url     : https://prove2.me/theorems/9db7226a-5270-48f6-a558-8a1088b6eba1
-- title:
--   Bounded conditional fine branches in fixed-round LOCC
-- statement:
--   Let $N,r,m\ge1$. Consider an $N$-party system with positive local dimensions $d_k$ and global dimension $D=\prod_kd_k$. Every $m$-outcome instrument $\mathcal J\in\mathrm{LOCC}_r$ has an $r$-round realization with a final classical coarse-graining such that, for each round $\ell\in\{1,\ldots,r\}$ and each conditional instrument in that round, the number of fine CP maps is at most
--   $$
--   mD^{4(r-\ell+1)}.
--   $$
--   Each fine CP map has the form $X\mapsto MXM^\dagger$ with a $D\times D$ matrix $M$. The communicating party may depend on the complete preceding public history. Local private Kraus records can be retained until the final coarse-graining and do not count as extra broadcasts. This supplies a finite operational witness and bounds every conditional instrument, rather than only the final number of outcomes.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 10, Theorem 2; Appendix A, pp.16–19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.10, Theorem 2; Appendix A, pp.16–19: a finite operational witness with a bound
on the single-Kraus refinement of every conditional instrument, not just the final leaves.
Round l=n+1 is guarded by n<r before evaluating r-n. Adaptive broadcasters are permitted. -/
theorem bounded_fine_branches {N r m : ℕ} (hN : 0 < N) (hr : 0 < r) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k)
    (J : Fin m → Superop (Config d) (Config d)) (hJ : InRounds d r J) :
    ∃ B : ℕ → ℕ → ℕ → Superop (Config d) (Config d),
      (∀ n, n < r → ∀ h, IsOneWay d (B n h) ∧
        HasFineBound d (B n h) (m * Fintype.card (Config d) ^ (4 * (r - n)))) ∧
      CoarseGrains (executeRounds B r) J := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

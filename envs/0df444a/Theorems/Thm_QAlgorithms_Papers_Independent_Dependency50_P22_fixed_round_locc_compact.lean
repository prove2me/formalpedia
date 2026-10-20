-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_fixed_round_locc_compact
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.fixed_round_locc_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:23:31.569319+00:00
-- url     : https://prove2.me/theorems/e28b35fe-e98c-44f1-a42b-25c3499be458
-- title:
--   Compactness for fixed rounds and fixed outcomes
-- statement:
--   Fix positive integers $N,r,m$ and positive local dimensions for an $N$-party system. Within the space $\mathrm{CP}[m]$ of instruments on these fixed coordinates and labels,
--   $$
--   \mathrm{LOCC}_r[m]\text{ is compact}.
--   $$
--   The topology is equivalently the QC diamond topology or the relative finite-dimensional topology of branch maps. Both $r$ and $m$ are fixed; this is the source's finite-round compactness result.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 10, Corollary 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.10, Corollary 3: both the round bound and the final outcome set are fixed. -/
theorem fixed_round_locc_compact {N r m : ℕ} (hN : 0 < N) (hr : 0 < r) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k) :
    IsCompact {J : {J : Fin m → Superop (Config d) (Config d) // IsInstrument J} |
      InRounds d r J.val} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

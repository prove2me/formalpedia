-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_locc_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.locc_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:19:19.620377+00:00
-- url     : https://prove2.me/theorems/bc51ae78-6c20-489f-8abf-a68b61d18aa9
-- title:
--   Convexity of LOCC instruments
-- statement:
--   Fix a positive finite number $N$ of parties, positive local dimensions, and a finite or countable outcome set $\Theta$. If $\mathcal J_1$ and $\mathcal J_2$ are LOCC instruments on these same input and output spaces with these same outcome labels, then for every $\lambda\in[0,1]$,
--   $$
--   \lambda\mathcal J_1+(1-\lambda)\mathcal J_2\in\mathrm{LOCC}.
--   $$
--   The mixture acts componentwise on the CP maps and uses no preshared entanglement. This identifies the operational class as a convex subset of the ambient instrument space, including infinite-round LOCC.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 8, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.8, Proposition 1: convexity for any fixed finite or countable label set. -/
theorem locc_convex {N : ℕ} (hN : 0 < N) (d : Fin N → ℕ)
    (hd : ∀ k, 0 < d k) (O : Type*) [Countable O] [DecidableEq O] :
    Convex ℝ {J : O → Superop (Config d) (Config d) | InLOCC d J} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

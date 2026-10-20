-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_depolarizing_ball_rounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.depolarizing_ball_rounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:22:00.338356+00:00
-- url     : https://prove2.me/theorems/8a5366f4-9bc0-4827-a684-f54e9078b9d9
-- title:
--   An explicit N-round LOCC ball
-- statement:
--   Let $N,m\ge1$, let $d_k\ge1$, and let $D=\prod_kd_k$. Write $\mathcal D_m$ for the equally weighted $m$-branch depolarizing instrument, and define
--   $$
--   R_{\mathrm{LOCC}}=\frac{R_{\mathrm{SEP}}}{m^2D^4}
--   =\bigl(m^3D^6 2^{N/2-1}+m^2D^4\bigr)^{-1},
--   \qquad R_{\mathrm{SEP}}=\bigl(mD^2 2^{N/2-1}+1\bigr)^{-1}.
--   $$
--   For every $m$-outcome instrument $\mathcal J$ on the fixed multipartite system,
--   $$
--   D_\diamond(\mathcal D_m,\mathcal J)\le R_{\mathrm{LOCC}}
--   \quad\Longrightarrow\quad \mathcal J\in\mathrm{LOCC}_N.
--   $$
--   The distance is the QC diamond distance without a factor of $1/2$, and $N$ counts communication rounds. The closed ball includes its depolarizing center.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 9, Corollary 2, Eq.(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF pp.9–10, Corollary 2: the closed QC-diamond ball has an N-round implementation.
No division by the actual distance is used, so its center is included. -/
theorem depolarizing_ball_rounds {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k)
    (J : Fin m → Superop (Config d) (Config d)) (hJ : IsInstrument J)
    (hbound : instrumentDistance (depolarizingInstrument m) J ≤
      loccRadius N m (Fintype.card (Config d))) : InRounds d N J := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

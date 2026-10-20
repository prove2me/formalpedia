-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_depolarizing_mixture_separable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.depolarizing_mixture_separable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:20:32.145612+00:00
-- url     : https://prove2.me/theorems/34181336-acf0-4b10-8a5f-f685e045e3b4
-- title:
--   A separable depolarizing mixture
-- statement:
--   Let $N,m\ge1$, let the local dimensions be positive, and set $D=\prod_{k=1}^N d_k$. For any $m$-outcome instrument $\mathcal J$, write $\mathcal D_m=(\mathcal D/m,\ldots,\mathcal D/m)$, where $\mathcal D(\rho)=\operatorname{Tr}(\rho)I_D/D$. Then
--   $$
--   0\le\eta\le R_{\mathrm{SEP}}:=\bigl(mD^2 2^{N/2-1}+1\bigr)^{-1}
--   \quad\Longrightarrow\quad
--   (1-\eta)\mathcal D_m+\eta\mathcal J\in\mathrm{SEP}.
--   $$
--   All branch labels remain fixed. This gives a source-specified amount of depolarizing noise sufficient to make every branch separable.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 9, Corollary 1, Eq.(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.9, Corollary 1, Eq.(5): J, not the identity map.
Printed: for all eta<=R_SEP, without a lower bound. Changed: require eta>=0.
Why: the proof uses a convex mixture; negative eta can make a branch nonpositive. -/
theorem depolarizing_mixture_separable {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k)
    (J : Fin m → Superop (Config d) (Config d)) (hJ : IsInstrument J)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hbound : eta ≤ sepRadius N m (Fintype.card (Config d))) :
    InSEP d ((1 - eta) • depolarizingInstrument m + eta • J) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end

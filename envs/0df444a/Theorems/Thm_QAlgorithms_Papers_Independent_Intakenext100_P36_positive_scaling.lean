-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_positive_scaling
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.positive_scaling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:17:03.074993+00:00
-- url     : https://prove2.me/theorems/80d1670a-04da-4263-9b0b-0671535965ee
-- title:
--   Positive scaling preserves the coefficient-change objective
-- statement:
--   Let $n,k\ge1$, let $p\ge0$, and let $E_i\in M_{k,n}$ and $F_i\in M_{n,k}$ be finite families. For invertible $S\in M_p$, put $G_j(S)=\sum_i(S^{-1})_{ij}E_i$, $H_i(S)=\sum_jS_{ij}F_j$, and
--
--   $$C(S)=\sqrt{\left\|\sum_iG_i(S)G_i(S)^\dagger\right\|}\sqrt{\left\|\sum_iH_i(S)^\dagger H_i(S)\right\|}.$$
--
--   For every positive definite $S$ and every positive real $c$, $C(cS)=C(S)$. Each positive definite $S$ admits a positive scalar multiple $cS$ with $0<cS\le I$ and the same cost. Consequently,
--
--   $$\inf_{S>0}C(S)=\inf_{0<S\le I}C(S).$$
--
--   The condition $0<S\le I$ means precisely that all eigenvalues lie in $(0,1]$. Empty families have zero cost.
--
--   This explains the sampling-domain normalization mathematically, without providing any sampling success or accuracy guarantee.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 17, §5, unnumbered normalization of the positive minimization domain

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- PDF p.17: scalar invariance and normalization of the positive domain.
For positive definite S, S <= I is equivalent to all eigenvalues belonging to (0,1].
Zero coefficient dimension is included, with empty objective equal to zero. -/
theorem positive_scaling {n k p : ℕ} (hn : 0 < n) (hk : 0 < k)
    (E : Fin p → Matrix (Fin k) (Fin n) ℂ)
    (F : Fin p → Matrix (Fin n) (Fin k) ℂ) :
    (∀ S : Mat p, S.PosDef → ∀ c : ℝ, 0 < c →
      changeCost E F ((c : ℂ) • S) = changeCost E F S) ∧
    (∀ S : Mat p, S.PosDef → ∃ c : ℝ, 0 < c ∧
      ((c : ℂ) • S).PosDef ∧ (1 - (c : ℂ) • S).PosSemidef ∧
      changeCost E F ((c : ℂ) • S) = changeCost E F S) ∧
    sInf {v : ℝ≥0∞ | ∃ S : Mat p, S.PosDef ∧
      v = ENNReal.ofReal (changeCost E F S)} =
    sInf {v : ℝ≥0∞ | ∃ S : Mat p, S.PosDef ∧ (1 - S).PosSemidef ∧
      v = ENNReal.ofReal (changeCost E F S)} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_stinespring_existence_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.stinespring_existence_uniqueness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:57:21.88736+00:00
-- url     : https://prove2.me/theorems/4c482192-2991-4a34-969f-920a08dc4f14
-- title:
--   Theorem 2: finite-dimensional Stinespring existence and partial-isometry uniqueness
-- statement:
--   Let $\Phi:\mathcal M(H_A)\to\mathcal M(H_B)$ be a CP map between finite complex spaces with $H_A\ne0$. There exist an environment of dimension $r\le(\dim H_A)(\dim H_B)$ and a linear $V:H_A\to H_B\otimes\mathbb C^r$ such that
--
--   $$\Phi(X)=\operatorname{Tr}_{\mathbb C^r}(VXV^*)\quad\text{for every }X.$$
--
--   If $\Phi$ is trace preserving then $V^*V=I_A$. For every alternative finite environment of arbitrary dimension $s$ and dilation $V'$ of the same map, a partial isometry $W:\mathbb C^r\to\mathbb C^s$ satisfies
--
--   $$V'=(I_B\otimes W)V,\qquad V=(I_B\otimes W^*)V'.$$
--
--   Zero environment dimension is allowed for the zero CP map. This preserves both equations of the source's uniqueness statement and the numerical environment bound.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 10, Theorem 2: finite-dimensional Stinespring existence and partial-isometry uniqueness

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Theorem 2, (19), PDF pp.10–11: dimension bound and BOTH intertwining
identities for arbitrary alternative environment. V is isometric only if TP. -/
theorem stinespring_existence_uniqueness [Nonempty A] (Phi : Superop A B) (hPhi : FiniteKrausCP Phi) :
    ∃ (r : ℕ) (V : Matrix (B × Fin r) A ℂ),
      r ≤ Fintype.card A * Fintype.card B ∧ receiverChannel V = Phi ∧ (IsChannel Phi → Vᴴ * V = 1) ∧
      ∀ (s : ℕ) (W : Matrix (B × Fin s) A ℂ), receiverChannel W = Phi →
        ∃ J : Matrix (Fin s) (Fin r) ℂ, PartialIsometry J ∧
          W = ((1 : Matrix B B ℂ) ⊗ₖ J) * V ∧ V = ((1 : Matrix B B ℂ) ⊗ₖ Jᴴ) * W := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end

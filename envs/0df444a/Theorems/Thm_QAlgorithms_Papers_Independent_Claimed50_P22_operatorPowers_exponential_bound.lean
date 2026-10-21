-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_operatorPowers_exponential_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.operatorPowers_exponential_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:10:18.538661+00:00
-- url     : https://prove2.me/theorems/9a38e5be-5441-4f81-b2e9-54efba482294
-- title:
--   Global exponential bound for operator powers
-- statement:
--   Let $V$ be a real or complex Banach space, and let $F:[0,\infty)\to L(V)$ satisfy $F(0)=1$. Let $M>0$ and $a\in\mathbb R$ satisfy $\|F(t)\|\le M e^{at}$ for all $t\ge0$. Suppose also that $\|F(t)^n\|\le M$ whenever $t\ge0$, $n\ge1$ is an integer, and $tn\le1$. Then
--
--   $$\exists\omega\in\mathbb R\ \forall t\ge0\ \forall n\ge1:\quad \|F(t)^n\|\le M e^{\omega nt}.$$
--
--   The powers are composition powers and the norms are operator norms. No continuity or differentiability of $F$ is assumed. The zero Banach space is allowed. The conclusion converts small-time stability into a uniform exponential power estimate.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 24, Lemma 8.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

/-- Lemma 8.1, PDF p. 24: a small-time power bound and a one-step
exponential bound imply a global exponential power bound. No continuity
or differentiability of F is assumed. Powers are composition powers. -/
theorem operatorPowers_exponential_bound
    {K : Type u} [RCLike K]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V] [CompleteSpace V]
    (F : Set.Ici (0 : ℝ) → (V →L[K] V)) (M a : ℝ) (hM : 0 < M)
    (hZero : F ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl)⟩ = 1)
    (hOne : ∀ t : Set.Ici (0 : ℝ), ‖F t‖ ≤ M * Real.exp (a * t.val))
    (hSmall : ∀ t : Set.Ici (0 : ℝ), ∀ n : ℕ, 0 < n →
      t.val * (n : ℝ) ≤ 1 → ‖F t ^ n‖ ≤ M) :
    ∃ omega : ℝ, ∀ t : Set.Ici (0 : ℝ), ∀ n : ℕ, 0 < n →
      ‖F t ^ n‖ ≤ M * Real.exp (omega * (n : ℝ) * t.val) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P22

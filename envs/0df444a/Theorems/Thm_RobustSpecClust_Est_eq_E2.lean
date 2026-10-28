-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E2
-- name    : RobustSpecClust.Est.eq_E2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:26.170335+00:00
-- url     : https://prove2.me/theorems/44ebb685-a705-44d9-b538-7dd613fc686a
-- title:
--   (E.2), p. 39 — ‖K_I − R_I‖₁ ≤ Σ_k m_c^(k,k) + Σ_{k≠l} m_c^(k,l)
-- statement:
--   Let $K$ be a matrix indexed by the $N$ points whose inlier block has entries in $[0,1]$, let $\tau_{\mathrm{in}} \in [0,1]$ and $\tau^{(k,l)}_{\mathrm{out}} \in [0,1]$ for $k \ne l$, and let $R$ be the reference matrix (6). Then
--   $$\|K_{\mathcal I} - R_{\mathcal I}\|_1 \le \sum_{k\in[r]}\sum_{i,j\in\mathcal C_k} \mathbb 1_{\{K_{ij}<\tau_{\mathrm{in}}\}}\,\tau_{\mathrm{in}} + \sum_{k\ne l}\sum_{i\in\mathcal C_k, j\in\mathcal C_l} \mathbb 1_{\{K_{ij}>\tau^{(k,l)}_{\mathrm{out}}\}}\big(1-\tau^{(k,l)}_{\mathrm{out}}\big) \le \sum_{k\in[r]} m_c^{(k,k)} + \sum_{k\ne l} m_c^{(k,l)} ,$$
--   where $m_c^{(k,k)}$ counts the pairs $(i,j) \in \mathcal C_k\times\mathcal C_k$ with $K_{ij} < \tau_{\mathrm{in}}$ and $m_c^{(k,l)}$ the pairs $(i,j)\in\mathcal C_k\times\mathcal C_l$ with $K_{ij} > \tau^{(k,l)}_{\mathrm{out}}$.
--
--   This reduces the $\ell_1$ distance between kernel and reference matrix to counting threshold violations ("corruptions"), which are then controlled probabilistically.
--
--   **Formalization Note** The middle expression is written as one double sum over all inlier pairs, split by whether the two labels agree.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.2), p. 39

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E2 {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ)
    (hK : ∀ i j, 0 ≤ inlierBlock K i j ∧ inlierBlock K i j ≤ 1)
    (hτin : 0 ≤ τin ∧ τin ≤ 1) (hτout : ∀ k l, k ≠ l → 0 ≤ τout k l ∧ τout k l ≤ 1) :
    l1 (inlierBlock K - inlierBlock (refMatrix K φ τin τout γ)) ≤
      ∑ i, ∑ j, (if φ i = φ j then (if K (Sum.inl i) (Sum.inl j) < τin then τin else 0)
        else (if τout (φ i) (φ j) < K (Sum.inl i) (Sum.inl j) then 1 - τout (φ i) (φ j) else 0)) ∧
    ∑ i, ∑ j, (if φ i = φ j then (if K (Sum.inl i) (Sum.inl j) < τin then τin else 0)
        else (if τout (φ i) (φ j) < K (Sum.inl i) (Sum.inl j) then 1 - τout (φ i) (φ j) else 0)) ≤
      ∑ k, (mcDiag K φ τin k : ℝ) + ∑ k, ∑ l ∈ Finset.univ.erase k, (mcOff K φ τout k l : ℝ) := by sorry

end RobustSpecClust.Est

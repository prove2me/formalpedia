-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_complete_bernstein_algebra
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.complete_bernstein_algebra
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:10:41.944559+00:00
-- url     : https://prove2.me/theorems/788c5da6-8641-4905-9348-8a6ee3dd63c6
-- title:
--   The complete Bernstein union is an algebra
-- statement:
--   On the cut plane $\Omega=\mathbb C\setminus(-\infty,0]$, let $\widetilde S_n$ be the complex linear span of the holomorphic extensions of generalised Stieltjes functions of positive integer order $n$. Let $\widetilde T_n=\{f:f(1/z)\in\widetilde S_n\}$ and $\widetilde T=\bigcup_{n\ge1}\widetilde T_n$. Then
--
--   $$\widetilde T_n\subseteq\widetilde T_m\quad(1\le n<m),\qquad \widetilde T_n\widetilde T_m\subseteq\widetilde T_{n+m}\quad(n,m\ge1).$$
--
--   Moreover, $\widetilde T$ is a unital complex algebra under pointwise operations on $\Omega$. The inversion characterisation is the equivalent definition stated after equation (4.12).
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 17, Proposition 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Proposition 4.7, PDF p.17: nesting, order-additive multiplication,
and the full algebra conclusion on a common cut-plane carrier. -/
theorem complete_bernstein_algebra :
    (∀ n m : ℕ, 0 < n → n < m → TildeTOrder n ⊆ TildeTOrder m) ∧
    (∀ n m : ℕ, 0 < n → 0 < m →
      ∀ f ∈ TildeTOrder n, ∀ g ∈ TildeTOrder m, f * g ∈ TildeTOrder (n + m)) ∧
    UnitalSubalgebraSet TildeT := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end

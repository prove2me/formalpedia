-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_general
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_general
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:19:56.094806+00:00
-- url     : https://prove2.me/theorems/f3efb17e-7f38-4d49-a3d5-e5be82b32d11
-- title:
--   Theorem 7.6 (Spectral Theorem: General Case)
-- statement:
--   Let $k\in\{\mathbb R,\mathbb C\}$ and let $H$ be any Hilbert space. Let $A_1,\ldots,A_d$ be closed densely defined normal operators, each self-adjoint if $k=\mathbb R$. For every pair of distinct indices $i,j$, suppose the four bounded transforms $T_{A_i},S_{A_i},T_{A_j},S_{A_j}$ commute pairwise, where $T_A=(I+A^*A)^{-1}$ and $S_A=AT_A$. Then
--
--   $$\exists!\ \Phi:M(k^d,\operatorname{Bo}(k^d))\to C(H)\text{ a measurable calculus with }\Phi(z_j)=A_j\quad(1\le j\le d).$$
--
--   Every finite-valued Borel symbol is included, and equality of coordinate images is equality of graphs and domains. No separability or boundedness of the operators is assumed. The empty tuple has base a singleton.
--
--   This is Theorem 7.6, the general joint spectral theorem.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 35, Theorem 7.6 (Spectral Theorem: General Case)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 7.6, PDF p.35: the full spectral theorem, real or complex, including all boundedGraph domains. -/
theorem spectral_general {d : ℕ} (A : Fin d → Relation H)
    (hH : CompleteSpace H) (hA : ∀ j, SpectralAdmissible (k := k) (A j))
    (hcomm : ∀ i j, i ≠ j → StronglyCommute (k := k) (A i) (A j)) :
    ∃! F : Symbol (Fin d → k) k → Relation H, Calculus F ∧
      ∀ j, F (fullCoordinate j) = A j := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end

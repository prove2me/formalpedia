-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_sigma_point_iff_countably_meet_closed
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.sigma_point_iff_countably_meet_closed
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:42:36.012477+00:00
-- url     : https://prove2.me/theorems/b855292c-d832-420b-9f2f-7f6fe1372b56
-- title:
--   Proposition 3.10
-- statement:
--   For a quasipoint $\mathfrak B$ in an abstract countably complete Boolean algebra, countable primeness is equivalent to closure under countable meets:
--
--   $$\mathfrak B\text{ is a point}\quad\Longleftrightarrow\quad
--   \bigwedge_{n\in\mathbb N}a_n\in\mathfrak B\ \text{whenever every }a_n\in\mathfrak B.$$
--
--   No underlying topological space is required; all joins and meets refer to their order-theoretic universal properties.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 50, Proposition 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.10; de Groote, Observables I, PDF p./pp. 50.
-/
theorem sigma_point_iff_countably_meet_closed {L : Type u} [BooleanAlgebra L] (hcomplete : IsSigmaComplete L)
    (B : StoneSpectrum L) :
    IsSigmaPoint B.val ↔ ∀ a : ℕ → L, (∀ n, a n ∈ B.val) →
      ∀ b : L, IsGLB (Set.range a) b → b ∈ B.val := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end

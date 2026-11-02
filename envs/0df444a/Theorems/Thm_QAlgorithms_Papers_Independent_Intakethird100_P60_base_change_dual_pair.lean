-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P60_base_change_dual_pair
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P60.base_change_dual_pair
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:28:24.660587+00:00
-- url     : https://prove2.me/theorems/6c34f543-b8a6-4144-a365-0371945e26ff
-- title:
--   Base change objects form a canonical dual pair
-- statement:
--   Let $\mathbb D$ be a framed bicategory and $f:A\to B$ a vertical arrow. Companion and conjoint objects $M=fB:A\rightsquigarrow B$ and $N=B_f:B\rightsquigarrow A$ exist. For every choice of their defining cells $u,c,v,d$ as in Theorem 4.1, set
--
--   $$
--   \eta:U_A\xrightarrow{\lambda^{-1}}U_A\odot U_A
--    \xrightarrow{u\odot v}M\odot N,
--   \qquad
--   \varepsilon:N\odot M\xrightarrow{d\odot c}U_B\odot U_B
--    \xrightarrow{\lambda}U_B.
--   $$
--
--   These maps satisfy both triangle identities, with the associator and unitors of $\mathbb D$. Thus $(M,N)$ is a dual pair, with $M$ the left adjoint and $N$ the right adjoint under diagrammatic composition.
--
--   The explicit maps make the duality canonical relative to the chosen base change cells.
-- source:
--   Framed bicategories and monoidal fibrations, arXiv:0706.1286v2, PDF p. 20, Proposition 5.3: Base change objects form dual pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P60

namespace QAlgorithms.Papers.Independent.Intakethird100.P60

open CategoryTheory

universe u v w x

/-- Proposition 5.3 (PDF pp. 20–21): the chosen companion and conjoint form
a dual pair with the displayed canonical evaluation and coevaluation. -/
theorem base_change_dual_pair {V : Type u} [Category.{v} V]
    (D : DoubleData.{u,v,w,x} V) (hD : DoubleCoherence D) (hFramed : IsFramed D)
    {A B : V} (f : A ⟶ B) :
    (∃ (M : D.H A B) (N : D.H B A),
      Nonempty (Companion D f M) ∧ Nonempty (Conjoint D f N)) ∧
    (∀ (M : D.H A B) (N : D.H B A) (c : Companion D f M) (j : Conjoint D f N),
      IsDualPair D M N (baseCoevaluation D c j) (baseEvaluation D c j)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P60

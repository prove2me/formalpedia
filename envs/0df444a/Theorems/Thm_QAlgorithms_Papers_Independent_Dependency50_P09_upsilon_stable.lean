-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_upsilon_stable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.upsilon_stable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:56:59.308532+00:00
-- url     : https://prove2.me/theorems/ca020854-bab5-43e7-9140-d1a9f998b1a7
-- title:
--   Proposition 12 (Stability)
-- statement:
--   Let $D$ be a dimension-consistent generalized divergence satisfying exactly (142)–(144): CPTP data processing, $D(1\Vert c)\ge0$ for $0<c\le1$, and $D(\rho\Vert\rho)=0$. Let $N$ be a bipartite channel and $E,F$ arbitrary finite local identity ancillas. Define $\Upsilon_D$ by (159),(161), using all CP comparisons with $\beta\le1$.
--
--   $$
--   \Upsilon_D(N)=\Upsilon_D(\operatorname{id}_E\otimes N\otimes\operatorname{id}_F).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The missing scalar-zero axiom is not added; stability uses preparation/discarding and DPI only.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 10, Proposition 12 (Stability)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 12 (Stability), arXiv:2010.01058v3, PDF pp.10.
The missing scalar-zero axiom is not added; stability uses preparation/discarding and DPI only. -/
theorem upsilon_stable {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    (div : Divergence) (hdiv : LawfulD div)
    (N : Superop (A × B) (C × D)) (hN : IsChannel N) :
    upsilon div N = upsilon div (stableMap (E := E) (F := F) N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end

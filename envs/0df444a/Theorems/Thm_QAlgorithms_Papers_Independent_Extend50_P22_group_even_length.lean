-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_group_even_length
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.group_even_length
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:36:21.866168+00:00
-- url     : https://prove2.me/theorems/d8008dba-8e74-4b42-b527-127790db22c2
-- title:
--   Unnumbered [[2m,2m−2,2]]G construction, Eqs.(68)–(70)
-- statement:
--   Let $G$ be finite and $m\ge2$. For logical labels $g_1,\ldots,g_{2m-2}$, form the alternating word $(1,g_1,g_2g_1,g_2g_3,\ldots,g_{2m-2}g_{2m-3},g_{2m-2})$ and average its collective left translates with coefficient $|G|^{-1/2}$. This is an isometry and corrects every one-site erasure. The $m-1$ independent right actions on odd-numbered logical labels are implemented on adjacent physical pairs, using inverse parameters. Consequently, $$[[2m,2m-2,2]]_G\quad\text{has transversal symmetry }G^{m-1}.$$ The degenerate $m=1$ member is also retained as the two-site, one-dimensional-logical orbit code.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 19, Unnumbered [[2m,2m−2,2]]G construction, Eqs.(68)–(70)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.18–19: [[2m,2m-2,2]]_G for every m>=2, with m-1 independent transversal factors. -/
theorem group_even_length (G : Type*) [Group G] [Fintype G] :
    (let V0 : Matrix (Fin 2 → G) Unit ℂ := orbitEncoding (fun g _ _ => g)
     V0ᴴ * V0 = 1 ∧ ∀ i : Fin 2, CorrectsGroupErasure V0 {i}) ∧
    ∀ k : ℕ, let V := evenEncoding G k
    Vᴴ * V = 1 ∧ (∀ i : Fin (2 * (k + 2)), CorrectsGroupErasure V {i}) ∧
    (∀ l : G, basisMapMatrix (fun y : Fin (2 * (k + 2)) → G => fun i => l * y i) * V = V) ∧
    ∀ r : Fin (k + 1) → G,
      basisMapMatrix (evenPhysical k r) * V = V * basisMapMatrix (evenLogical k r) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end

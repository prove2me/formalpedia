-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_group_four
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.group_four
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:34:45.9414+00:00
-- url     : https://prove2.me/theorems/1163c7ec-7629-44b0-91a5-fb8b665eade7
-- title:
--   Unnumbered [[4,2,2]]G code, Eqs.(65)–(66)
-- statement:
--   Let $G$ be any finite group. The normalized isometry is $$V|a,b\rangle=|G|^{-1/2}\sum_{g\in G}|g,g^{-1}a,gb,g^{-1}ab\rangle.$$ Every one-site erasure has an exact CPTP recovery for all logical states. The logical action $(a,b)\mapsto(la,br^{-1})$ is implemented by the physical site actions $(y_1,y_2,y_3,y_4)\mapsto(ly_1,y_2,ly_3r^{-1},y_4r^{-1})$. This exhibits the transversal $G\times G$ symmetry, with the required noncommutative product order.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 18, Unnumbered [[4,2,2]]G code, Eqs.(65)–(66)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.18, (65),(66): exact single erasures and transversal G x G symmetry.
The right multiplier uses r^-1 so this is a representation of G rather than G^op. -/
theorem group_four (G : Type*) [Group G] [Fintype G] :
    let V := groupFourEncoding G
    Vᴴ * V = 1 ∧ (∀ i : Fin 4, CorrectsGroupErasure V {i}) ∧
    ∀ l r : G,
      basisMapMatrix (fun y : Fin 4 → G =>
        ![l * y 0, y 1, l * y 2 * r⁻¹, y 3 * r⁻¹]) * V =
      V * basisMapMatrix (fun x : G × G => (l * x.1, x.2 * r⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end

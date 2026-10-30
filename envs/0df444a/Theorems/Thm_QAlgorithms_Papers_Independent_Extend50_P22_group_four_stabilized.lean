-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_group_four_stabilized
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.group_four_stabilized
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:35:32.752433+00:00
-- url     : https://prove2.me/theorems/d1b68356-c51d-4790-886d-1847ddf674bf
-- title:
--   Unnumbered stabilized [[4,2,2]]G variant, Eq.(67)
-- statement:
--   Let $G$ be finite and define $$V|a,b\rangle=|G|^{-1/2}\sum_{g\in G}|g,ga,gba,gb\rangle.$$ This is an isometry correcting every single-site erasure. Simultaneous left multiplication of all physical coordinates fixes every codeword, while right multiplication by $r^{-1}$ on the second and third sites implements $(a,b)\mapsto(ar^{-1},b)$. Thus the code has the stated transversal $G$ symmetry. The larger independent symmetry of the distinct four-site construction is not asserted.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 18, Unnumbered stabilized [[4,2,2]]G variant, Eq.(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.18, (67): collective-left invariance and only the stated one-factor logical G
symmetry, together with correctability of each single erasure. -/
theorem group_four_stabilized (G : Type*) [Group G] [Fintype G] :
    let V := stabilizedFourEncoding G
    Vᴴ * V = 1 ∧ (∀ i : Fin 4, CorrectsGroupErasure V {i}) ∧
    (∀ l : G, basisMapMatrix (fun y : Fin 4 → G => fun i => l * y i) * V = V) ∧
    ∀ r : G,
      basisMapMatrix (fun y : Fin 4 → G => ![y 0, y 1 * r⁻¹, y 2 * r⁻¹, y 3]) * V =
        V * basisMapMatrix (fun x : G × G => (x.1 * r⁻¹, x.2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end

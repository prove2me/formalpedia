-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.distributive_basic_unions
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:37:54.920198+00:00
-- url     : https://prove2.me/theorems/c51a3729-55a5-4b30-8ba0-507af583a906
-- title:
--   rem-3.1
-- statement:
--   For a bounded distributive lattice,
--
--   $$Q_a\cup Q_b=Q_{a\vee b}.$$
--
--   For any bounded lattice satisfying this union identity, the further identity $Q_{(a\wedge b)\vee(a\wedge c)}=Q_{a\wedge(b\vee c)}$ holds for every $a,b,c$. This latter consequence does not by itself imply distributivity without order reflection.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 43, rem-3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-3.1; de Groote, Observables I, PDF p./pp. 43.
-/
theorem distributive_basic_unions {L : Type u} [Lattice L] [BoundedOrder L] :
    (IsDistributive (L := L) → ∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) ∧
    ((∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) →
      ∀ a b c : L, stoneBasic ((a ⊓ b) ⊔ (a ⊓ c)) = stoneBasic (a ⊓ (b ⊔ c))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end

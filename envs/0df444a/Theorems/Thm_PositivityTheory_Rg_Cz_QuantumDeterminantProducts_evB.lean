-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evB
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evB
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:34.131556+00:00
-- url     : https://prove2.me/theorems/55223b32-0b75-4a03-8004-af9084648eb8
-- title:
--   Quantum Determinant Products: ev B
-- statement:
--   The Quantum Determinant Products construction uses the ev B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L150-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L150-L197

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evB (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (I : Fin n → Fin n) :
    ev E u l I h = ∑ c ∈ Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ l → c p = I p),
      (l.map fun k : Fin n => Tm E (u - (k : ℂ)) (c k) (I k)).prod (h c) := by sorry

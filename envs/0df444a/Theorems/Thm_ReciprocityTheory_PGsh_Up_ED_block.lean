-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_block
-- name    : ReciprocityTheory.PGsh.Up.ED.block
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:28.62446+00:00
-- url     : https://prove2.me/theorems/6182004f-5897-5d22-bab3-55ba339b9af9
-- title:
--   ED: block
-- statement:
--   The ED construction uses the block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L30-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L30-L344

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.ED.block (hv : v.Integers R) {ι κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ']
    [DecidableEq κ'] (Φ : Matrix κ' ι R)
    (ε : Matrix ι ι R) (hε : ε * ε = ε) (Pq : Matrix κ' κ' R) (Qs : Submodule R (κ' → R))
    (hPqmem : ∀ w, Pq *ᵥ w ∈ Qs) (hPqid : ∀ w ∈ Qs, Pq *ᵥ w = w) (hcomm : Φ * ε = Pq * Φ)
    (n : ℕ) (hnT : Module.finrank R (LinearMap.range (Matrix.mulVecLin ε)) = n)
    (hnQ : Module.finrank R Qs = n) (X : NNReal)
    (hX : HasLen v R (Qs ⧸ ((LinearMap.range (Matrix.mulVecLin ε)).map (Matrix.mulVecLin Φ)).comap
      Qs.subtype) X)
    (cp : R) (hcp : ∀ w : ι → R, w ᵥ* ε = w → ∃ u : κ' → R, cp • w = u ᵥ* (Φ * ε)) :
    ∃ (lam : Fin n → ι → R) (a : Fin n → R) (y : Fin n → ι → R),
      (∀ j, lam j ᵥ* ε = lam j) ∧ (∀ l, ε *ᵥ y l = y l) ∧
      (∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0) ∧ (∀ j, ∃ c, cp = a j * c) ∧
      ∏ j, v (algebraMap R C (a j)) = X ∧
      Submodule.span R (Set.range fun k => (Φ * ε) k) =
        Submodule.span R (Set.range fun j => a j • lam j) := by sorry

-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_prod_map_pow_single
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.prod_map_pow_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:24.166463+00:00
-- url     : https://prove2.me/theorems/684dd114-0ae5-4446-a108-6e7cbb65eb1e
-- title:
--   Core Bb: prod map pow single
-- statement:
--   The Core Bb construction uses the prod map pow single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L26-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreBb.prod_map_pow_single {M : Type*} [Monoid M] {ι : Type*} [DecidableEq ι] (P : ι → M)
    (hP : ∀ i j, Commute (P i) (P j)) (e : ι → ℕ) (k : ι) :
    ∀ L : List ι, L.Nodup → k ∈ L →
      (L.map fun i => P i ^ (e i + if i = k then 1 else 0)).prod = (L.map fun i => P i ^ e i).prod * P k
  := by sorry

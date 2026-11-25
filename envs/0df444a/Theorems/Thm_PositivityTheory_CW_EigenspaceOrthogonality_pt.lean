-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_pt
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.pt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:13.072288+00:00
-- url     : https://prove2.me/theorems/6180616b-81ae-4832-a6bb-e5c30a736a21
-- title:
--   Eigenspace Orthogonality: pt
-- statement:
--   The Eigenspace Orthogonality construction uses the pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L49-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L49-L66

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

theorem PositivityTheory.CW.EigenspaceOrthogonality.pt (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (a b : Fin n) (x y : V) :
    inner ℂ (E a b (E c d x)) (A (E a b y)) =
      inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)
      + (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0)
      - (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) := by sorry

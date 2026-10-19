-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_minimumEntanglementGraphBranch
-- name    : QAlgorithms.Papers.Independent.Information100.P22.minimumEntanglementGraphBranch
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:08:01.397643+00:00
-- url     : https://prove2.me/theorems/5011f797-0baf-448a-ad32-136498c716ff
-- title:
--   §III B / S2.4, unnumbered: minimum-entanglement graph branch
-- statement:
--   Let $m\ge2$ be odd, $k\ge1$, and fix a graph cut and distinct encoder axes. If the entire cut kernel is exceptional and $\dim K=k$, then the axes belong to YZ/ZY and
--   $$r=S(\rho_S)=(m-1)k.$$
--   By contrast, an exactly recoverable XZ/ZX realization has $r\ge(m-1)k+1$. Thus only the YZ/ZY class can attain the entropy floor within this fixed graph Pauli frame. This is conditional saturation, not an existence assertion from rank-nullity alone.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 8, §III B / S2.4, unnumbered: minimum-entanglement graph branch

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- PDF pp.8,32: saturation is conditional on the complete kernel inclusion and maximal nullity. -/
theorem minimumEntanglementGraphBranch (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hodd : Odd m) (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k)) :
    ((Module.finrank F2 (cutKernel G) = k ∧
      (cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) →
      classYZ P Q ∧ G.B.rank = (m-1)*k ∧
      vnEntropy (rhoS (graphVector G)) = (((m-1)*k : ℕ) : ℝ)) ∧
    (classXZ P Q → AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) →
      (m-1)*k+1 ≤ G.B.rank) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22

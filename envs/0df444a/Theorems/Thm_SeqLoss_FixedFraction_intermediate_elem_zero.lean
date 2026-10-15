-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_intermediate_elem_zero
-- name    : SeqLoss.FixedFraction.intermediate_elem_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:59.53478+00:00
-- url     : https://prove2.me/theorems/4a0bfbeb-b661-430a-a6f9-a6991d588539
-- title:
--   Proof of Proposition 2, p. 23 — population monotonicity and merging proofness give $\varphi_i(e_n)=0$ for $1<i<n$
-- statement:
--   Let $\varphi$ be a rule satisfying population monotonicity and merging proofness. Then for each $n\ge 3$ and each intermediate agent $1<i<n$,
--   $$\varphi_i(e_n)=0 .$$
--
--   Together with the end-point identities, this shows that on elementary problems such a rule shares the unit loss only between the initiator and the last agent.
--
--   **Formalization Note.** 0-based: the agent $i$ ranges over indices with $1\le i$ and $i+1<n$ (so $n\ge 3$ is implied). Population monotonicity is Axiom 3 with the corrected range $1\le j<n$ (see the Axioms item).
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix A, p. 23, proof of Proposition 2, (⟹), third display and the sentence after it

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem intermediate_elem_zero (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (i : Fin n)
    (hi1 : 1 ≤ i.val) (hin : i.val + 1 < n) :
    φ n (elem n) i = 0 := by sorry

end SeqLoss.FixedFraction

-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_phi2_e3_eq_zero
-- name    : SeqLoss.FixedFraction.phi2_e3_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:04.566075+00:00
-- url     : https://prove2.me/theorems/7ef27af7-9534-4871-b5ec-0d65d299c365
-- title:
--   Proof of Proposition 2, p. 23 — merging proofness forces $\varphi_2(e_3)=0$
-- statement:
--   Let $\varphi$ be a rule satisfying merging proofness. Then the intermediate agent of the elementary problem $e_3=(0,0,1)$ carries no liability:
--   $$\varphi_2(e_3)=0 .$$
--
--   This is the first step of the proof that population monotonicity and merging proofness pin down a rule on elementary problems; it relies on the balance $\varphi_1(e_3)+\varphi_2(e_3)+\varphi_3(e_3)=1=\varphi_1(e_2)+\varphi_2(e_2)$ and non-negativity of allocations.
--
--   **Formalization Note.** 0-based: $\varphi_2(e_3)$ is `φ 3 (elem 3) 1`.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix A, p. 23, proof of Proposition 2, (⟹), second display

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem phi2_e3_eq_zero (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hmp : MergingProof φ) :
    φ 3 (elem 3) 1 = 0 := by sorry

end SeqLoss.FixedFraction

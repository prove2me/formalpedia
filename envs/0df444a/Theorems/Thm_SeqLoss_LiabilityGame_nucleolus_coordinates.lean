-- Prove2me | Theorems.Thm_SeqLoss_LiabilityGame_nucleolus_coordinates
-- name    : SeqLoss.LiabilityGame.nucleolus_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:28.510544+00:00
-- url     : https://prove2.me/theorems/ba422927-6125-44cd-91d1-e8fe51691b61
-- title:
--   Proof of Theorem 3, p. 24 — the nucleolus of $v_\ell$ gives $\nu_i=M_i(v_\ell)/2=\ell_i/2$ for $i\neq1$, and $\nu_1=\varphi^{1/2}_1(\ell)$ by balance
-- statement:
--   Let $\ell\in\mathcal L^n$ with $n\ge1$, let $v_\ell$ be the liability game and let $\nu$ be a nucleolus of $v_\ell$ (an imputation whose non-increasingly sorted excess vector is lexicographically minimal among imputations). Then for every agent $i\neq1$
--   $$\nu_i=\frac{M_i(v_\ell)}{2}=\frac{\ell_i}{2}=\varphi^{1/2}_i(\ell),$$
--   and for the initiator $\nu_1=\varphi^{1/2}_1(\ell)=\tfrac12\ell_1+\tfrac12L$.
--
--   The paper obtains this from Muto et al. (1988, Theorem 4.2), the nucleolus formula for big boss games, and efficiency ("balance") of the nucleolus. Together with the existence of the nucleolus it pins it down as $\varphi^{1/2}(\ell)$.
--
--   **Formalization Note.** The statement is about every $x$ satisfying `IsNucleolus (liabilityGame ℓ) x`, so it also contains the uniqueness of the nucleolus of $v_\ell$; existence is not asserted here (it follows from the next milestone). The chain of equalities is stated link by link, with $M_i$ the `marginalContribution` of the definition file and the initiator at index `0`.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 24, Appendix A, proof of Theorem 3, second paragraph (citing Muto, Nakayama, Potters & Tijs 1988, Theorem 4.2)

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game
import Definitions.Def_SeqLoss_LiabilityGame_Nucleolus

namespace SeqLoss.LiabilityGame

theorem nucleolus_coordinates {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ)
    (x : Fin n → ℝ) (hx : IsNucleolus (liabilityGame ℓ) x) :
    (∀ i : Fin n, i ≠ 0 →
      x i = marginalContribution (liabilityGame ℓ) i / 2 ∧
      marginalContribution (liabilityGame ℓ) i / 2 = ℓ i / 2 ∧
      ℓ i / 2 = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ i) ∧
    x 0 = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ 0 := by sorry

end SeqLoss.LiabilityGame

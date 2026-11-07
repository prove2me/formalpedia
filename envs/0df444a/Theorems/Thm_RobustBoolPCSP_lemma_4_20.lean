-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_20
-- name    : RobustBoolPCSP.lemma_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:12.515633+00:00
-- url     : https://prove2.me/theorems/d0b00bc4-e6c1-4523-9014-542116664634
-- title:
--   Lemma 4.20 (Simulations) — $R_{\mathsf A}$ simulates some $\mathsf A_k$, $R_{\mathsf M}$ simulates some $\mathsf C_t$ or $\mathsf B_r$
-- statement:
--   Let $R_{\mathsf A}$ and $R_{\mathsf M}$ be relation pairs with properties (i) and (ii) of Lemma 4.18, $R_{\mathsf M}=(P,Q)$ having symmetric $Q$ and $P\subseteq Q$ like every pair of the template there. Then
--
--   1. $R_{\mathsf A}$ simulates $\mathsf A_k=(\mathrm{Ham}_k(\{(k+1)/2\}),\mathrm{NAND}_k)$ for some odd $k\ge3$;
--   2. $R_{\mathsf M}$ simulates $\mathsf C_t$ for some $t\ge3$, or $\mathsf B_r$ for some $r\ge2$,
--
--   in the sense of Lemma 4.19, by lists of signed constraints on the single pair.
--
--   With Lemma 4.19 and Theorem 4.9 this yields the perfect integrality gap of case (ii) of the dichotomy.
--
--   Differences from the source:
--   - reading: R_A and R_M as in Lemma 4.18 → any pairs with property (i), resp. property (ii) together with symmetric Q and P ⊆ Q; reason: these are the properties Lemma 4.18 provides; symmetry and P ⊆ Q hold for every pair of its template and survive global negation
--   - encoding: R_A simulates A_k in the sense of Lemma 4.19 → Simulates (Template.single P Q) (AkP k) (NAND k): a list of signed constraints of the single pair R_A; reason: the lemma simulates each canonical pair by one witness pair
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.20, p.26

import Mathlib
import Definitions.Def_RobustBoolPCSP_WitnessPairs
import Definitions.Def_RobustBoolPCSP_Simulation

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Lemma 4.20 (Simulations)**, p.26. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let RA and RM be as in Lemma 4.18. Then RA simulates some Ak, and RM simulates some Ct or some Br,
in the sense of Lemma 4.19."

**Formalization Note.** `R_𝖠 = (P, Q)` is any pair with property (i) of Lemma 4.18
(`IsWitnessRA`), `R_𝖬 = (P, Q)` any pair with property (ii) (`IsWitnessRM`) that is, like every pair
of the template of Lemma 4.18 after global negation, symmetric with `P ⊆ Q`. "Simulates" uses lists
of signed constraints of the single pair (`Simulates (Template.single P Q)`). `𝖠_k` is for odd
`k ≥ 3`, `𝖢_t` for `t ≥ 3`, `𝖡_r` for `r ≥ 2` (§4.3, p.21). -/
theorem lemma_4_20 :
    (∀ (n : ℕ) (P Q : Set (Fin n → Bool)), IsWitnessRA P Q →
      ∃ k : ℕ, Odd k ∧ 3 ≤ k ∧ Simulates (Template.single P Q) (AkP k) (NAND k)) ∧
    (∀ (n : ℕ) (P Q : Set (Fin n → Bool)), IsWitnessRM P Q → IsSymmetricRel Q → P ⊆ Q →
      (∃ t : ℕ, 3 ≤ t ∧ Simulates (Template.single P Q) (CtP t) (CtQ t)) ∨
      (∃ r : ℕ, 2 ≤ r ∧ Simulates (Template.single P Q) (BrP r) (NAND r))) := by sorry

end RobustBoolPCSP

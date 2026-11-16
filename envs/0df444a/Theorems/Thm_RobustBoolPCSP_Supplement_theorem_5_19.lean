-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_5_19
-- name    : RobustBoolPCSP.Supplement.theorem_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:33:52.658592+00:00
-- url     : https://prove2.me/theorems/fab41692-3a49-432d-99c9-dfc54db3dcf4
-- title:
--   Theorem 5.19 (Argmax equivalence) — mode property ⟺ separating certificates; $\mathfrak P\subseteq\mathrm{MC}\subseteq\mathrm{CS}_{\mathrm{out}}$
-- statement:
--   Let $(P,W)$ be a pair on $A$ of positive arity with $q=|A|\ge2$, and let $\rho$ be any argmax selector (it returns a label of maximal score). Then
--
--   $$(P,W)\ \text{has the mode property}\iff(P,W)\ \text{has separating certificates for }\rho.$$
--
--   Consequently
--
--   $$\mathfrak P\subseteq\mathrm{MC}\subseteq\mathrm{CS}_{\mathrm{out}}.$$
--
--   Nullary pairs, and all pairs when $q=1$, are treated alike by the two notions: for them the mode property is exactly $P\subseteq W$, which is what Definition 5.13 requires.
--
--   Differences from the source:
--   - encoding: any argmax selector, that is, any selector returning a label of maximal score with a fixed tie rule → any function ρ with z(ρ z) ≥ z a for all z, a; reason: such a function is an argmax selector with its own tie rule, and conversely
--   - reading: nullary relation pairs, and templates with q = 1, are treated by the mode property and by Definition 5.13 in the same way → for P, W ⊆ A^0, and for P, W ⊆ A^r when |A| = 1: ModeProperty P W ↔ P ⊆ W; reason: Definition 5.13 asks exactly P_j ⊆ W_j in these cases
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 5.19, p.41

import Mathlib
import Definitions.Def_RobustBoolPCSP_ModeProperty
import Definitions.Def_RobustBoolPCSP_Supplement_Classes
import Definitions.Def_RobustBoolPCSP_Supplement_ConsSep

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 5.19 (Argmax equivalence)**, p.41. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let (P, W) be a pair on A of positive arity, with q ≥ 2, and fix any argmax selector, that is, any
selector returning a label of maximal score with a fixed tie rule. Then (P, W) has the mode property
if and only if it has separating certificates for this selector. Consequently, 𝔓 ⊆ MC ⊆ CS_out;
nullary relation pairs, and templates with q = 1, are treated by the mode property and by
Definition 5.13 in the same way."

**Formalization Note.** Four conjuncts: (1) the equivalence, for every selector `ρ` returning a
maximal label; (2) `𝔓 ⊆ MC` for same-domain templates (`InPlur`, `InMC`); (3) `MC ⊆ CS_out`
(`InCSout`); (4) the last sentence: for a nullary pair, and for any pair when `q = 1`, the mode
property is `P ⊆ W`, which is what Definition 5.13 requires in those cases. -/
theorem theorem_5_19 :
    (∀ {A : Type} [Fintype A] [DecidableEq A], 2 ≤ Fintype.card A → ∀ {r : ℕ}, 1 ≤ r →
      ∀ (P W : Set (Fin r → A)) (ρ : (A → ℝ) → A), IsArgmaxSel ρ →
        (ModeProperty P W ↔ HasSepCerts ρ P W)) ∧
    (∀ {ι A : Type} [Fintype ι] [Fintype A] [DecidableEq A] [Nonempty A] (T : Template ι A A),
      InPlur T → InMC T) ∧
    (∀ {ι A B : Type} [Fintype ι] [Fintype A] [DecidableEq A] [Nonempty A] (T : Template ι A B),
      InMC T → InCSout T) ∧
    (∀ {A : Type} [Fintype A] [DecidableEq A],
      (∀ P W : Set (Fin 0 → A), ModeProperty P W ↔ P ⊆ W) ∧
      (Fintype.card A = 1 → ∀ {r : ℕ} (P W : Set (Fin r → A)), ModeProperty P W ↔ P ⊆ W)) := by sorry

end RobustBoolPCSP.Supplement

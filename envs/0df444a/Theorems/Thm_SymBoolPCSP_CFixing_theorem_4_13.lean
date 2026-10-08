-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_theorem_4_13
-- name    : SymBoolPCSP.CFixing.theorem_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:08.56818+00:00
-- url     : https://prove2.me/theorems/6c3ae40f-78d2-4b78-8ed9-a9e983db6fa2
-- title:
--   Theorem 4.13 — folded symmetric Γ avoiding Par, AT, Maj and their antis has only C(Γ)-fixing polymorphisms
-- statement:
--   Let $\Gamma$ be a finite, folded, symmetric family of Boolean promise relations. Assume that there are odd $L_1, \dots, L_6$ such that
--   $$\mathrm{Par}_{L_1},\ \mathrm{AT}_{L_2},\ \mathrm{Maj}_{L_3},\ \overline{\mathrm{Par}}_{L_4},\ \overline{\mathrm{AT}}_{L_5},\ \overline{\mathrm{Maj}}_{L_6}$$
--   are not polymorphisms of $\Gamma$, where $\overline{g} = \neg g$. Then there is a constant $C(\Gamma)$ such that every polymorphism of $\Gamma$, of every arity $L$, is $C(\Gamma)$-fixing: for each such $f$ there is $S \subseteq [L]$ with $|S| \le C(\Gamma)$ and $f(x) = f(0, \dots, 0)$ whenever $x$ vanishes on $S$.
--
--   Here $\mathrm{Par}_L(x) = x_1 \oplus \dots \oplus x_L$, $\mathrm{Maj}_L(x) = [\sum_i x_i > L/2]$ and $\mathrm{AT}_L(x) = [\sum_{i=1}^L (-1)^{i-1} x_i > 0]$. Combined with the Label Cover reduction of §5 (Theorem 5.3), this structural statement gives the NP-hardness half of the paper's dichotomy for folded symmetric Boolean PCSPs (Theorem 2.16).
--
--   **Formalization Note** Only the structural statement is formalized; the NP-hardness conclusion of Theorems 2.16 and 5.3 is out of scope. Polymorphisms of every arity $L \ge 0$ are quantified, as in the published `IsPolymorphism`; a folded family has no nullary polymorphisms, so this changes nothing. The constant $C$ precedes $L$ and $f$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 25, Theorem 4.13

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Theorem 4.13 (p. 25): let `Γ` be a finite, folded, symmetric family of Boolean promise
relations, and assume there are odd `L₁, …, L₆` such that `Par_{L₁}`, `AT_{L₂}`, `Maj_{L₃}`,
`¬Par_{L₄}`, `¬AT_{L₅}` and `¬Maj_{L₆}` are not polymorphisms of `Γ`. Then there is `C(Γ)` such that
all polymorphisms of `Γ` (of every arity) are `C(Γ)`-fixing. -/
theorem theorem_4_13 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹)
    (L₁ L₂ L₃ L₄ L₅ L₆ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂) (hL₃ : Odd L₃) (hL₄ : Odd L₄)
    (hL₅ : Odd L₅) (hL₆ : Odd L₆)
    (h₁ : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (h₂ : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (h₃ : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃))
    (h₄ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₄ → Bool => !Par L₄ x))
    (h₅ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₅ → Bool => !AT L₅ x))
    (h₆ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₆ → Bool => !Maj L₆ x)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f := by sorry

end SymBoolPCSP.CFixing

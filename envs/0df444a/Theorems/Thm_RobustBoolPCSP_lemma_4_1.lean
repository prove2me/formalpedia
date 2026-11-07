-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_1
-- name    : RobustBoolPCSP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:33.104014+00:00
-- url     : https://prove2.me/theorems/d41966d8-3b46-4d31-a2b0-73406cc7c05a
-- title:
--   Lemma 4.1 (Literal compilation) — signed instances become ordinary instances of a finite template $\hat\Gamma$
-- statement:
--   Let $\Gamma$ be a finite Boolean template. There is a finite Boolean template $\hat\Gamma$ with the following properties.
--
--   1. Every signed instance $I$ of $\Gamma$ corresponds to an ordinary instance of $\hat\Gamma$ on the same variables with the same number of constraints, such that every assignment $b$ has the same strong and weak errors in both:
--   $$\mathrm{err}_{\mathrm{str}}(b;\hat I)=\mathrm{err}_{\mathrm{str}}(b;I),\qquad \mathrm{err}_{\mathrm{wk}}(b;\hat I)=\mathrm{err}_{\mathrm{wk}}(b;I).$$
--   2. Every folded idempotent polymorphism of $\Gamma$ is a polymorphism of $\hat\Gamma$.
--   3. If $\Gamma$ is symmetric with $P_j\subseteq Q_j$ for every $j$, then $\hat P\subseteq\hat Q$ for every pair $(\hat P,\hat Q)$ of $\hat\Gamma$.
--
--   The lemma lets algorithms for ordinary templates run on signed instances, with constants compiled away.
--
--   Differences from the source:
--   - encoding: relation pairs indexed by [m] → relation pairs indexed by a finite type ι; reason: a finite index type is in bijection with [m]
--   - reading: every signed instance corresponds to an ordinary instance of Γ̂ → a map comp n from the constraint lists of signed instances on n variables to constraint lists of Γ̂ on the same n variables, fixed with Γ̂ before the instances; the ordinary instance of I is ⟨I.n, comp I.n I.cons⟩; reason: "on the same variables" fixes the variable set; Γ̂ does not depend on the instance
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.1, Lemma 4.1, p.16

import Mathlib
import Definitions.Def_RobustBoolPCSP_Signed

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Lemma 4.1 (Literal compilation)**, p.16. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"There is a finite Boolean template Γ̂ with the following properties. Every signed instance of Γ
corresponds to an ordinary instance of Γ̂ with the same number of constraints, on the same
variables, such that every assignment has the same strong and weak errors in both. Every folded
idempotent polymorphism of Γ is a polymorphism of Γ̂. If Γ is symmetric with Pj ⊆ Qj, then Γ̂
satisfies P̂ ⊆ Q̂ for each of its pairs."

**Formalization Note.** `Γ̂` has a finite index type `ι'`, chosen before the instances. The
correspondence is a map `comp n` from constraint lists over `Fin n` with literals to constraint lists
of `Γ̂` over the same variables `Fin n`; the ordinary instance of `I` is `⟨I.n, comp I.n I.cons⟩`.
Polynomial time of the correspondence is not part of the lemma. -/
theorem lemma_4_1 {ι : Type} [Fintype ι] (Γ : Template ι Bool Bool) :
    ∃ (ι' : Type) (_ : Fintype ι') (Γhat : Template ι' Bool Bool)
      (comp : (n : ℕ) → List (Σ j : ι, Fin (Γ.r j) → Literal n) →
        List (Σ j : ι', Fin (Γhat.r j) → Fin n)),
      (∀ I : SignedInstance Γ,
        (comp I.n I.cons).length = I.cons.length ∧
        ∀ b : Fin I.n → Bool,
          (⟨I.n, comp I.n I.cons⟩ : Instance Γhat).errStr b = I.errStr b ∧
          (⟨I.n, comp I.n I.cons⟩ : Instance Γhat).errWk b = I.errWk b) ∧
      (∀ (L : ℕ) (F : (Fin L → Bool) → Bool), IsFolded F → IsIdempotent F → IsPolB Γ F →
        IsPolB Γhat F) ∧
      (IsSymmetricTemplate Γ → IsPromiseTemplate Γ → IsPromiseTemplate Γhat) := by sorry

end RobustBoolPCSP

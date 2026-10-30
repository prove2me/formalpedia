-- Prove2me | Theorems.Thm_Schwichtenberg1976_combinators_and_sufficiency
-- name    : Schwichtenberg1976.combinators_and_sufficiency
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:54:21.086566+00:00
-- url     : https://prove2.me/theorems/4694e83f-7878-4185-8cdf-964a0d906b8a
-- title:
--   Classification of Closed Normal Terms of Type `ν` and Sufficiency for Extended Polynomials
-- statement:
--   Every closed β-normal term of type `ν` is α-equivalent to a Church numeral `n̄` or `λα. α`; the explicit combinators `addComb`, `mulComb`, `constComb`, and `condComb` define `+`, `·`, constants, and `d(n, m, i)`; and every extended polynomial (`IsExtendedPolyInd`) is λ-definable over `ν`.
-- source:
--   Helmut Schwichtenberg, 'Definierbare Funktionen im λ-Kalkül mit Typen', Archiv für mathematische Logik und Grundlagenforschung 17, 1975/1976, pp. 113-114 (doi:10.1007/BF02011242). pp. 113-114.

import Definitions.Def_Schwichtenberg1976_Lambda

namespace Schwichtenberg1976

/-- First part of Schwichtenberg's characterization (pp. 113–114):
1. Every closed β-normal term of type `ν = (0 → 0) → (0 → 0)` is α-equivalent to a
   Church numeral `n̄` or the identity `λα. α`.
2. `addComb`, `mulComb`, `constComb c`, and `condComb` define addition, multiplication,
   the unary constant `c`, and the conditional `d(n, m, i)` on Church numerals.
3. Every function in the inductive class of extended polynomials (`IsExtendedPolyInd`)
   is λ-definable over `ν`. -/
theorem combinators_and_sufficiency :
    (∀ t : Term,
      HasType t Ty.nu →
      IsClosed t →
      IsBetaNormal t →
      (∃ n : Nat, AlphaEq t (churchNumeral n)) ∨
      (∃ α : Var, α.ty = Ty.endo ∧ AlphaEq t (.lam α (.var α)))) ∧
    DefinesFunction 2 addComb (fun v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩) ∧
    DefinesFunction 2 mulComb (fun v => v ⟨0, by decide⟩ * v ⟨1, by decide⟩) ∧
    (∀ c : Nat, DefinesFunction 1 (constComb c) (fun _ => c)) ∧
    DefinesFunction 3 condComb
      (fun v => condNat (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) (v ⟨2, by decide⟩)) ∧
    (∀ {k : Nat} {f : (Fin k → Nat) → Nat},
      IsExtendedPolyInd f → IsLambdaDefinable k f) := by
  sorry

end Schwichtenberg1976

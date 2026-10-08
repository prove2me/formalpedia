-- Prove2me | Theorems.Thm_ProximityPadeErrorLineCount_mca_scalar_prime_error_card_le
-- name    : ProximityPadeErrorLineCount.mca_scalar_prime_error_card_le
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T16:33:09.137985+00:00
-- url     : https://prove2.me/theorems/893d3f32-7b5e-40ae-9dd1-f5b667a200c5
-- title:
--   At most p+1 MCA parameters with scalar prime-field error words
-- statement:
--   Let K be any field of prime characteristic p, let S be a finite set of Frobenius-fixed nodes (x^p=x), and let 0<k≤|S|. The two original polynomial words Y₀,Y₁ have arbitrary coefficients in K. For every counted affine parameter γ, allow its own support T⊆S and its own polynomial P of natural degree less than k, fitting Y₀+γY₁ on T. Require that the two originals do not both admit degree-less-than-k fits on that same T.
--
--   Assume additionally that the error of this same P over the entire domain S has the form
--
--   Y₀(x)+γY₁(x)−P(x)=η·v(x),
--
--   where η∈K and v takes values in the prime subfield of K. The scale η may be zero, and T, P, η and v may all depend on γ. Then the number of distinct counted parameters is at most p+1. Node zero is allowed; no shared support, finite extension degree, minimum support size, or prime-field-valued original words are assumed.
--
--   The proof uses the high coefficients of each word modulo the nodal polynomial as parity coordinates. Prime-field-valued normalized errors imply prime-field-valued remainder coefficients by Frobenius and interpolation uniqueness. Independent parity vectors give a projective subline count of p+1; dependent vectors give at most one parameter, while a globally coded second word excludes every same-support nontrivial parameter.
--
--   This is a restricted-error-structure MCA theorem. An upstream argument must still establish the whole-domain error premise for any intended parameter family. This result does not assert that premise universally, does not prove a complete δ=0 stratum theorem, and does not establish a full protocol certificate or numerical improvement for the proximity benchmark.
-- source:
--   Original research during the Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575, in the setting of https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270 . Frozen source theorem ProximityPadeErrorLineCount.mca_scalar_prime_error_card_le has SHA-256 fa078f00273e0cf8e867d0682981e2449fa2e2d3579046dded9b95e5010864cd; its six-module Mathlib-only proof closure was independently replayed locally. The standalone provider proof contains those arguments and relies only on the pinned Mathlib environment. No full benchmark theorem or official score change is attributed to this result.
--
--   yukon-proof-operation:7b5139d8-90c7-4d51-ab87-03e8771d4168; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTFiM2MxMmI0YWZhMTdlZTJkMWM0MWY2ZjNiYWI0ZGFjZTU2MThiZWIzMjk0ZWU0MTdmMzliMTZhYjcxZGYzZiIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjdiNTEzOWQ4LTkwYzctNGQ1MS1hYjg3LTAzZTg3NzFkNDE2ODsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVBhZGVFcnJvckxpbmVDb3VudC5tY2Ffc2NhbGFyX3ByaW1lX2Vycm9yX2NhcmRfbGUiLCJ2IjoyfQ]

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Polynomial

theorem ProximityPadeErrorLineCount.mca_scalar_prime_error_card_le {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (k : ℕ) (hk : 0<k) (hkS : k≤S.card)
    (hS : ∀ x∈S, x^p=x) (Y₀ Y₁ : K[X]) (Γ : Finset K)
    (hΓ : ∀ γ∈Γ, ∃ T : Finset K, T⊆S ∧ ∃ P : K[X],
      P.natDegree<k ∧ (∀ x∈T, P.eval x=Y₀.eval x+γ*Y₁.eval x) ∧
      (¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=Y₀.eval x) ∧ (∀ x∈T, P₁.eval x=Y₁.eval x)) ∧
      ∃ η : K, ∃ v : K → (⊥ : Subfield K), ∀ x∈S,
        Y₀.eval x+γ*Y₁.eval x-P.eval x=η*(v x : K)) :
    Γ.card≤p+1 := by
  sorry

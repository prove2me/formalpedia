-- Prove2me | Theorems.Thm_WICanon_theorem_2_7
-- name    : WICanon.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:44.701196+00:00
-- url     : https://prove2.me/theorems/91a5c054-9656-4481-8b6f-2058275fc110
-- title:
--   Theorem 2.7 ([IL89]) — distributional one-way functions imply one-way functions
-- statement:
--   If there exists an auxiliary-input distributional one-way function, then there exists an auxiliary-input one-way function.
--
--   The statement has two clauses: the printed one, and its infinitely-often form, which is the one the proof of Theorem 3.3 uses (p.17): an infinitely-often distributional AI-OWF on a set of valid indices gives infinitely-often AI-OWFs.
--
--   **Formalization Note** The resulting family is length preserving, as Definition 2.5 asks.
--
--   Differences from the source:
--   - generalization: the printed non-io implication → also the infinitely-often implication over an index set valid; reason: Theorem 3.1's alternative 1 and the conclusion of Theorem 3.3 are infinitely-often, so the proof on p.17 needs this form; the first clause is the printed one
--   - reading: SD ≥ ε for every n → for all sufficiently large n; reason: at n = 1 the bound SD ≥ 1 is defeated by a finite table for every family, so the printed hypothesis would be empty
--   - reading: codomain {0,1}^m(n) in Definition 2.6 → free codomain; reason: Theorem 3.1's family outputs prefixes of varying length and Theorem 3.7's has codomain {0,1}^ℓ(n)
--   - generalization: m polynomial → m polynomially bounded and computable from 1^n; reason: transcript domains contain ⌈log₂ L⌉ bits; a polynomial is an instance
--   - generalization: PPT A on (a, f_a(x)) → PPT A on (1^n, a, f_a(x)); reason: a machine ignoring 1^n is the printed adversary, so the Lean conclusion implies the printed one
--   - encoding: efficiently computable family indexed by a → one machine on (1^n, a, x); reason: when λ and m are both constant the family is trivially invertible, otherwise n is polynomially readable from the lengths
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 2.7, p.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_AIOWF
import Definitions.Def_WICanon_DistAIOWF

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity

/-- **Theorem 2.7** ([IL89]; distributional one-way functions imply one-way functions). Arnon, Mazor, Pass,
Silbak, *Does Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256
3f78ec3d…), p.12. If there exists an auxiliary-input distributional one-way function then there exists an
auxiliary-input one-way function.

**Formalization Note.** Two clauses. The first is the printed one, for all large `n` (Definition 2.6 with its
reading). The second is the infinitely-often form, over an index set `valid`, which the proof of Theorem 3.3
needs on p.17: Theorem 3.1's alternative 1 is infinitely-often, and so is the conclusion of Theorem 3.3. The
codomain of the given family is free and its domain length `m` is any polynomially bounded function a
machine can compute. The output family is length preserving, as Definition 2.5 asks. -/
theorem theorem_2_7 :
    (∀ (lam : Polynomial ℕ) (m : ℕ → ℕ) (f : ℕ → Str → Str → Str), IsPolyLen m →
      EfficientOn (fun n a => a.length = lam.eval n) m f →
      IsDistAIOWF (fun n a => a.length = lam.eval n) m f → AIOWFExist) ∧
    (∀ (valid : ℕ → Str → Prop) (lam : Polynomial ℕ) (m : ℕ → ℕ) (f : ℕ → Str → Str → Str),
      (∀ n a, valid n a → a.length = lam.eval n) → IsPolyLen m → EfficientOn valid m f →
      IsIODistAIOWF valid m f → IOAIOWFExist) := by sorry

end WICanon

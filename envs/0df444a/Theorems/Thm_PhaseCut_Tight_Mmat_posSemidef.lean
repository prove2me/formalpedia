-- Prove2me | Theorems.Thm_PhaseCut_Tight_Mmat_posSemidef
-- name    : PhaseCut.Tight.Mmat_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:20.700986+00:00
-- url     : https://prove2.me/theorems/421ada26-f42d-4875-9bae-ff94f67ff7ca
-- title:
--   §2.2, p. 4 — M = diag(b)(I − AA†)diag(b) is positive semidefinite
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be injective, with pseudoinverse $A^\dagger=(A^*A)^{-1}A^*$, and let $b\in\mathbb R^n$ be arbitrary. Then the Hermitian matrix
--
--   $$M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b)$$
--
--   is positive semidefinite.
--
--   The matrix $\mathbf I-AA^\dagger$ is the orthogonal projector onto the orthogonal complement of the range of $A$. Positive semidefiniteness of $M$ makes the quadratic problem (2), $\min u^*Mu$ over unit-modulus $u$, and its relaxation PhaseCut bounded below by $0$; it is used in the proof of Proposition 4.2.
--
--   **Formalization Note** The paper states this for every $A$. Here $A^\dagger$ is encoded as $(A^*A)^{-1}A^*$, which is the pseudoinverse only when $A$ is injective, so injectivity is added as a hypothesis; it is the standing assumption of the whole mission.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, §2.2, pp. 3–4 (sentence after (2); cited p. 4)

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- §2.2, p. 4: for injective `A` (so that `pinv A` is `A†`) and any real `b`, the matrix
`M = diag(b)(I − AA†)diag(b)` is positive semidefinite. -/
theorem Mmat_posSemidef {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) :
    (Mmat A b).PosSemidef := by sorry

end PhaseCut.Tight

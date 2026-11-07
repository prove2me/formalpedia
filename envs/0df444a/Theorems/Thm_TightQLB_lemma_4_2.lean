-- Prove2me | Theorems.Thm_TightQLB_lemma_4_2
-- name    : TightQLB.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:02:56.828848+00:00
-- url     : https://prove2.me/theorems/421a3aba-1c2d-4abf-b684-1448048c7f72
-- title:
--   Lemma 4.2 — key inequality, $\|b_zg\|^2+\|(D_z-I)g\|^2\le\|g\|^2+\|b_z^2g\|^2$
-- statement:
--   For every $g\in\mathcal F$ and every $z\in\{0,1\}^n$, with $D_z=b_z^\dagger b_z$,
--
--   $$
--   \|b_zg\|^2+\|(D_z-I)g\|^2\le\|g\|^2+\|b_z^2g\|^2 .
--   $$
--
--   This is the step that bounds the single-removal term of the score by the progress measure, and it keeps the gap $\|(D_z-I)g\|^2$ used in the paper's later analysis.
--
--   Differences from the source:
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: H = A ⊗ E and the space F of functions f ↦ Φ(f) ∈ H → any finite index type H, with Φ : (Qubits n → Bool) → H → ℂ; reason: coordinates in a finite orthonormal basis
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Lemma 4.2, p. 24 (PDF p. 27), Eq. (28)

import Mathlib
import Definitions.Def_TightQLB_Recording
open QAlgorithms

namespace TightQLB

/-- **Lemma 4.2 (Key inequality)**, p.24 (PDF p.27), Eq. (28).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"For every g ∈ F and every z ∈ {0,1}^n, ‖b_z g‖² + ‖(D_z − I)g‖² ≤ ‖g‖² + ‖b_z² g‖²."

**Formalization Note.** `D_z = b_z† b_z`, so `(D_z − I)g` is `bOpAdj z (bOp z g) - g`. `H` is an
arbitrary finite type; `n ≥ 1` is not needed. -/
theorem lemma_4_2 {n : ℕ} {H : Type} [Fintype H] (g : Fn n H) (z : Qubits n) :
    nsq (bOp z g) + nsq (bOpAdj z (bOp z g) - g) ≤ nsq g + nsq (bOp z (bOp z g)) := by sorry

end TightQLB

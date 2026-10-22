-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_lemma_8
-- name    : QMCProduct.HalfApprox.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:03.490816+00:00
-- url     : https://prove2.me/theorems/fc125506-77b9-4964-9ee3-e423024c694e
-- title:
--   Lemma 8, p. 22 — if M(p, q, r) ⪰ 0 and q ≤ 0, then p ≥ −√3/2
-- statement:
--   Let $M(p,q,r)$ be the real $4\times4$ SWAP Gram matrix displayed in Section 4.3. If $M(p,q,r)$ is positive semidefinite and $q\le0$, then
--   $$p\ge-\frac{\sqrt3}{2}.$$
--   The bound rules out a sufficiently negative SWAP value on one edge alongside a nonpositive value on an adjacent edge.
--
--   **Formalization Note** The statement follows the printed lemma. The proof's displayed dual certificate has a coordinate-order erratum, recorded in the moderation notes.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 22, Lemma 8

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Lemma 8, p. 22. -/
theorem lemma_8 (p q r : ℝ) (hM : (swapGram p q r).PosSemidef) (hq : q ≤ 0) :
    -(Real.sqrt 3) / 2 ≤ p := by sorry

end QMCProduct.HalfApprox

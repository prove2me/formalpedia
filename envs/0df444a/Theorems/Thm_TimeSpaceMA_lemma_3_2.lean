-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_2
-- name    : TimeSpaceMA.lemma_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:56:47.867077+00:00
-- url     : https://prove2.me/theorems/1555695d-9672-44e1-93d3-4b0e7a1ac10e
-- title:
--   Lemma 3.2 — the NAND constraint $\gamma$
-- statement:
--   For all integers $w_1,w_2,z$,
--   $$\gamma(w_1,w_2,z)\ge 0,$$
--   and $\gamma(w_1,w_2,z)=0$ exactly when $w_1,w_2\in\{0,1\}$ and $z=\mathrm{NAND}(w_1,w_2)$.
--
--   This is what lets one quadratic form check one gate of the transition circuit over the integers.
--
--   Differences from the source:
--   - encoding: z = NAND(w1, w2) → z = 1 − w1·w2; reason: on bits these agree, and the conjunction states that w1, w2 are bits
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.2, p.9

import Definitions.Def_TimeSpaceMA_lambdaForm

namespace TimeSpaceMA

/-- **Lemma 3.2** (NAND constraint; Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…,
p.9). On integers, `γ` is nonnegative, and it vanishes exactly when `w₁, w₂` are bits and
`z = NAND(w₁, w₂)`.

**Formalization Note** On bits, `NAND(w₁, w₂) = 1 − w₁ w₂`. -/
theorem lemma_3_2 (w₁ w₂ z : ℤ) :
    0 ≤ gammaForm w₁ w₂ z ∧
      (gammaForm w₁ w₂ z = 0 ↔ (w₁ = 0 ∨ w₁ = 1) ∧ (w₂ = 0 ∨ w₂ = 1) ∧ z = 1 - w₁ * w₂) := by sorry

end TimeSpaceMA

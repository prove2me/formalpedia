-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_1
-- name    : QPVEntanglement.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:12.484479+00:00
-- url     : https://prove2.me/theorems/72dd797c-dcd6-460b-ad2f-eb48fe53424c
-- title:
--   Lemma 1 — classical-record direct sum
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $\omega_{XAB}=\sum_xp_x|x\rangle\langle x|_X\otimes\omega^x_{AB}$, where $\{|x\rangle\}$ is an orthonormal basis and Alice holds the classical register $X$. Then
--
--   $$E_{sq}(AX:B)_\omega=\sum_xp_xE_{sq}(A:B)_{\omega^x}.$$
--
--   It lets squashed entanglement be evaluated by averaging over a classical record held on one side.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: Alice's register AX → the state on (X × A) × B (`recordOnLeft`); reason: the order of the two factors of Alice's register does not change E_sq
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 1, p.27; proof p.63

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 1 (Classical-Record Direct Sum)**, p.27 (proof p.63). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 1, p.27.

If `ω_{XAB} = Σ_x p_x |x⟩⟨x|_X ⊗ ω^x_{AB}` with Alice holding the classical register `X`, then
`E_sq(AX : B)_ω = Σ_x p_x E_sq(A : B)_{ω^x}`.

**Formalization Note.** The state is `recordOnLeft p ω` on `(X × A) × B` (Alice's register
`XA`; the order of her two factors is immaterial). `E_sq` is the published `squashed` (bits,
½·inf over every finite extension). -/
theorem lemma_1 {X A B : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (p : X → ℝ) (ω : X → Matrix (A × B) (A × B) ℂ)
    (hp : IsProbVec p) (hω : ∀ x, IsDensity (ω x)) :
    squashed (recordOnLeft p ω) = ∑ x, p x * squashed (ω x) := by sorry

end QPVEntanglement

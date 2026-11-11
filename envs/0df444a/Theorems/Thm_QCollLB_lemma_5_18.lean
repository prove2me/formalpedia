-- Prove2me | Theorems.Thm_QCollLB_lemma_5_18
-- name    : QCollLB.lemma_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:18:38.599195+00:00
-- url     : https://prove2.me/theorems/704f7eef-1a28-494e-a95f-3bc968bac9d9
-- title:
--   Lemma 5.18 — projected forward-query comparison
-- statement:
--   There is a universal constant $C$ such that for $t+3\le n/8$,
--   $$
--   \|K_D O_iV-VO_i\|_{P_{\le t}}\le C\frac{t+1}n,\qquad \|O_iV-VO_i\|_{P_{\le t}}\le C\sqrt{\frac{t+1}n},
--   $$
--   where on the left $O_i=C_iD_iC_i$ is the auxiliary query on the database and on the right $O_i$ is the genuine forward query on the permutation register. The estimates hold uniformly for arbitrary phase vectors, ancillary registers, and coherent control of the query position and answer label.
--
--   The second bound is what lets the genuine permutation process be compared with the auxiliary database process.
--
--   Differences from the source:
--   - reading: uniformity "for arbitrary phase vectors, ancillary registers, and coherent control of the query position and answer label" → one statement for every finite control register Λ selecting a position i(ℓ) and a phase vector g(ℓ) of unit-modulus phases on the n slots and the blank; reason: this is the uniform statement printed after (50); the fixed-(i,c) case is Λ a singleton with g the standard phases
--   - encoding: operator norm restricted to P_{≤t} → ‖X h‖ ≤ c‖h‖ for all h ∈ P_{≤t} ⊗ ℂ[Λ]; reason: equivalent definition of the restricted norm
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 5.18, Eqs. (49)–(50), p.36, continued p.37

import Mathlib
import Definitions.Def_QCollLB_Harmonic
import Definitions.Def_QCollLB_Queries

namespace QCollLB

open CompPermOracle

/-- **Lemma 5.18 (Projected forward-query comparison)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Lemma 5.18, Eqs. (49)–(50), p.36, with its continuation p.37). For `t + 3 ≤ n/8`, with
a universal constant `C`: `‖K_D O_i V − V O_i‖_{P_{≤t}} ≤ C(t + 1)/n` (49) and
`‖O_i V − V O_i‖_{P_{≤t}} ≤ C √((t + 1)/n)` (50). "The estimates hold uniformly for arbitrary phase
vectors, ancillary registers, and coherent control of the query position and answer label."

**Formalization Note.** On the left `O_i` is the auxiliary query `C_i D_{i,g} C_i` on `D`
(Definition 5.3), on the right the genuine forward query `|π⟩ ↦ g(π(i))|π⟩` on `P` (Definition 3.2).
The uniformity is stated in the strongest form: a control register `Λ` (an arbitrary finite type,
which includes ancillas) selects the position `i(ℓ)` and a phase vector `g(ℓ)` of unit-modulus
phases for the `n` slots and the blank (p.23); the operator norm on `P_{≤t} ⊗ ℂ[Λ]` is written as
`‖X h‖ ≤ c ‖h‖` for all `h` in that subspace. `C` is chosen before `n, t, Λ, i, g`. -/
theorem lemma_5_18 :
    ∃ C : ℝ, ∀ (n t : ℕ), ((t : ℝ) + 3 ≤ (n : ℝ) / 8) →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (i : Λ → Fin n) (g : Λ → Option (Fin n) → ℂ),
        (∀ l z, ‖g l z‖ = 1) →
        ∀ h ∈ ampSub (Λ := Λ) (PLe n t),
          ‖opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (KD n)
              (auxCtl i g (opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (V n) h)) -
            opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (V n) (genCtl i g h)‖ ≤
              C * (((t : ℝ) + 1) / n) * ‖h‖ ∧
          ‖auxCtl i g (opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (V n) h) -
            opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (V n) (genCtl i g h)‖ ≤
              C * Real.sqrt (((t : ℝ) + 1) / n) * ‖h‖ := by sorry

end QCollLB

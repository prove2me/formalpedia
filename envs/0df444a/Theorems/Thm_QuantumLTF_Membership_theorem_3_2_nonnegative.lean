-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_2_nonnegative
-- name    : QuantumLTF.Membership.theorem_3_2_nonnegative
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:06:09.340948+00:00
-- url     : https://prove2.me/theorems/5fbeca03-5881-44f7-9889-8615156dcbe1
-- title:
--   Theorem 3.2 for nonnegative format constants
-- statement:
--   The coherent height-oracle construction of Theorem 3.2 in the nonvacuous case where both supplied fixed-point format constants are nonnegative.
-- source:
--   Nonvacuous core of Theorem 3.2 in Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Theorem 3.2 (Coherent implementation of height function).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.2, p. 23 (PDF p. 24).
For `n ≥ 2`, `0 < ϵ ≤ 1/2`, on the event `1/10 ≤ |⟨w, p⟩| ≤ 3`, given `s = sign(⟨w, p⟩)` and `h̃_p(0)` with
`|h̃_p(0) − h_p(0)| ≤ ϵ/100`, for `ρ = 2^{−⌈log₂(40√n)⌉}`, `H_p(x) := h_p(ρx)` and every `0 < η < 1/8`, there
is a reversible circuit `|x⟩|0⟩ ↦ |x⟩|H̃_p(x)⟩` with `|H̃_p(x) − H_p(x)| ≤ η` for every `x ∈ G_b^n`, using
`O(log(1/η))` queries to `O_{f_{w,θ}}` and `O(n (b + log n + log(1/ϵ) + log(1/η))² log(1/η))` other gates.

**Formalization Note.** The circuit may depend on `p, s, h̃` (the section conditions on them) but not
on `w, θ`; `H̃` may depend on `w, θ`. Hypotheses on the formats of `p` (`O(log n)` bits, Lemma 3.1) and
`h̃` (`O(log(1/ϵ))` bits, Theorem 3.1 at `ζ = ϵ/100`), which the gate bound rests on (pp. 25–26), appear
with universal `C₁, C₂` before `C`. The width of the value register, `O(log(1/ϵ) + log(1/η))`
(p. 30), is a further conclusion. Work wires return to `|0⟩`. -/
theorem theorem_3_2_nonnegative (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (b : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / η) ∧
          (c.gateCount : ℝ) ≤ C * n *
            (b + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 * Real.log (1 / η) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η := by sorry

end QuantumLTF.Membership

-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_3_nonnegative
-- name    : QuantumLTF.Membership.theorem_3_3_nonnegative
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T11:10:54.804285+00:00
-- url     : https://prove2.me/theorems/f4cfb46e-b775-4c18-b7af-8e9306876e15
-- title:
--   Theorem 3.3 for a nonnegative format constant
-- statement:
--   The gradient-estimation circuit of Theorem 3.3 in the nonvacuous case where the supplied value-register format constant is nonnegative.
-- source:
--   Nonvacuous core of Theorem 3.3 in Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Theorem 3.3 (Gradient estimation).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.3, p. 27 (PDF p. 28), Eqs. (49)–(51). For
`n ≥ 2`, under the conditions of Theorem 3.2 with `0 < ϵ ≤ 1/2`, let `g := ∇h_p = −w/⟨w, p⟩`, `0 < ϵ_g ≤ 10`,
`0 < γ ≤ 1/2`, `η := ρϵ_g / (48π(3n+1))`, `b := ⌈log₂((3n+1)/(ρϵ_g))⌉`. Given an oracle
`O_H : |x⟩|0⟩ → |x⟩|H̃_p(x)⟩` with `|H̃_p(x) − H_p(x)| ≤ η` for every `x ∈ G_b^n`, one calculates `g̃ ∈ Rⁿ` with
`‖g̃ − g‖_∞ ≤ ϵ_g` with probability at least `1 − γ`, using `O(log(1/γ))` queries to `O_H` and its inverse
and `O((n log²(n/ϵ_g) + log(1/ϵ)) log(1/γ))` other gates.

**Formalization Note.** `O_H` is any unitary with the stated action on `|x⟩|0⟩|0⟩`. The circuit depends on
the register format but not on `w, θ, p, O_H`. Of the conditions of Theorem 3.2 only
`1/10 ≤ |⟨w, p⟩| ≤ 3` is kept: the statement does not use `s` or `h̃` (a generalization). `queryCount` counts `O_H` and its inverse. The classical
median of p. 30 is inside the circuit. The value register has `O(log(1/ϵ) + log(1/η))` bits (p. 30),
a hypothesis with universal `C₁` before `C`. -/
theorem theorem_3_3_nonnegative (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg γ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < εg → εg ≤ 10 →
      0 < γ → γ ≤ 1 / 2 →
      let η : ℝ := rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / γ) ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) *
            Real.log (1 / γ) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |readFp (oa i) fo z - (-(w i) / inner ℝ w p)| ≤ εg) ≥ 1 - γ := by sorry

end QuantumLTF.Membership

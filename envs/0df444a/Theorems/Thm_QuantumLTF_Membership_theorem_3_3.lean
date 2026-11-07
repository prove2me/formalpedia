-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_3
-- name    : QuantumLTF.Membership.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:36:38.602041+00:00
-- url     : https://prove2.me/theorems/edebc17c-6920-4a36-8f54-37e6a3fd04c5
-- title:
--   Theorem 3.3 — gradient estimation from an approximate height oracle
-- statement:
--   Let $n\ge2$, $0<\epsilon\le1/2$, $0<\epsilon_g\le10$, $0<\gamma\le1/2$, and set
--   $$\eta:=\frac{\rho\epsilon_g}{48\pi(3n+1)},\qquad b:=\left\lceil\log_2\frac{3n+1}{\rho\epsilon_g}\right\rceil.$$
--   Let $g:=\nabla h_p=-w/\langle w,p\rangle$ with $w$ a unit vector and $1/10\le|\langle w,p\rangle|\le3$. Suppose $O_H$ is a unitary with $O_H:|x\rangle|0\rangle\mapsto|x\rangle|\tilde H_p(x)\rangle$ and
--   $$|\tilde H_p(x)-H_p(x)|\le\eta\quad(x\in G_b^n),$$
--   where $H_p(x)=h_p(\rho x)$. Then a circuit, independent of $w,\theta,p,O_H$, yields $\tilde g\in\mathbb R^n$ with $\|\tilde g-g\|_\infty\le\epsilon_g$ with probability at least $1-\gamma$, using $O(\log(1/\gamma))$ queries to $O_H$ and its inverse and
--   $$O\left(\left(n\log^2\frac n{\epsilon_g}+\log\frac1\epsilon\right)\log\frac1\gamma\right)$$
--   additional gates. This is Jordan's algorithm with the robust analysis of [GAW19], applied to an exactly affine function.
--
--   Differences from the source:
--   - reading: O(·) in a statement → one universal constant C placed before n and the other parameters; reason: the O(·) of the paper is uniform in all the stated parameters
--   - reading: the conditions of Theorem 3.2 and a value register of unstated size → hypothesis: value register of ≤ C₁ (log(1/ϵ) + log(1/η)) bits, with ∀ C₁ before ∃ C; reason: p. 30, "The fixed-point height value uses O(log(1/ϵ) + log(1/η)) bits", which the gate bound uses
--   - generalization: the conditions of Theorem 3.2 (good event, s, h̃_p(0)) → only the good event 1/10 ≤ |⟨w, p⟩| ≤ 3 is kept; reason: the proof uses no property of s or h̃; fewer hypotheses imply the printed statement
--   - encoding: oracle O_H : |x⟩|0⟩ → |x⟩|H̃_p(x)⟩ → any unitary with this action on |x⟩|0⟩|0⟩, with W work wires; reason: the theorem specifies the oracle only on these states
--   - generalization: gate complexity (51) of non-oracle gates, with the median as classical bit operations → the classical median is inside the circuit and counted in gateCount; reason: Eq. (62) gives the bound for the sum; the circuit is measured at the end
--   - encoding: a vector g̃ ∈ Rⁿ → fixed-point numbers read from wires; reason: the proof reads g̃ᵢ = kᵢ/ρ with kᵢ ∈ G_b, a fixed-point number since ρ is a power of 2
--   - reading: additional gates → unitaries on one or two qubits; reason: §C.5, p. 95; §3 names no other model
--   - generalization: membership queries, unspecified as to control → every oracle call is plain or inverse, with no control wire; reason: the proof uses no controlled query; an uncontrolled circuit is a special case of a circuit with any queries
--   - reading: we can calculate a vector g̃ ∈ Rⁿ → one circuit, with its output format, chosen before w, θ, p, H̃ and O_H; reason: the algorithm sees them only through O_H; the circuit of pp. 28–30 uses only n, b, γ and the register format
--   - encoding: the value H̃_p(x) in the register of O_H, and grid points x ∈ G_b^n → the Vb value wires read as fpVal Vb Vf; a basis state of n registers of b qubits is the point (g_b(x_1), …, g_b(x_n)); reason: as in Theorem 3.2; g_b is a bijection onto G_b (p. 23)
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.3, Eqs. (49)–(51), p. 27 (PDF p. 28)

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
theorem theorem_3_3 (C₁ : ℝ) :
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

-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_2
-- name    : QuantumLTF.Membership.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:19.980947+00:00
-- url     : https://prove2.me/theorems/167fe805-fc5b-49c9-9690-963fab2b43f8
-- title:
--   Theorem 3.2 — coherent implementation of the height function
-- statement:
--   Let $n\ge2$, $0<\epsilon\le1/2$, $0<\eta<1/8$, $b\in\mathbb N$, $\rho=2^{-\lceil\log_2(40\sqrt n)\rceil}$, and $H_p(x):=h_p(\rho x)$. Let $p$ have coordinates of $O(\log n)$ bits, and let $s$ and $\tilde h_p(0)$ be given, the latter with $O(\log(1/\epsilon))$ bits. There is a reversible circuit, depending on these data but not on $w,\theta$, with $O(\log(1/\eta))$ queries to $O_{f_{w,\theta}}$ and
--   $$O\left(n\left(b+\log n+\log\frac1\epsilon+\log\frac1\eta\right)^2\log\frac1\eta\right)$$
--   additional gates, such that for every unit $w$ and $\theta$ with $1/10\le|\langle w,p\rangle|\le3$, $s=\mathrm{sign}(\langle w,p\rangle)$ and $|\tilde h_p(0)-h_p(0)|\le\epsilon/100$, it maps
--   $$|x\rangle|0\rangle\longmapsto|x\rangle|\tilde H_p(x)\rangle,\qquad|\tilde H_p(x)-H_p(x)|\le\eta\quad(x\in G_b^n).$$
--   The value register has $O(\log(1/\epsilon)+\log(1/\eta))$ bits and work wires return to $|0\rangle$. This provides the value oracle consumed by gradient estimation.
--
--   Differences from the source:
--   - reading: O(·) in a statement → one universal constant C placed before n and the other parameters; reason: the O(·) of the paper is uniform in all the stated parameters
--   - reading: p from Lemma 3.1 and h̃_p(0) from Theorem 3.1 at ζ = ϵ/100 → hypotheses: p has coordinates of ≤ C₁ log n bits and h̃ has ≤ C₂ log(1/ϵ) bits, with ∀ C₁ C₂ before ∃ C; reason: the theorem refers to these results for its data, and the gate bound rests on the formats (pp. 25–26)
--   - generalization: |x⟩|0⟩ ↦ |x⟩|H̃_p(x)⟩ with no size claim for the value register → also concludes that the value register has ≤ C (log(1/ϵ) + log(1/η)) bits and work wires return to |0⟩; reason: p. 25 and p. 30 prove these; Theorem 3.3 needs the register size, and removing the conclusion gives the printed statement
--   - encoding: reversible circuit → an oracle circuit over NOT, CNOT, Toffoli, with work wires starting in |0⟩; reason: p. 26 names these gates; the oracle is applied through OracleCircuit.unitary
--   - encoding: O_{f_{w,θ}} on real addresses → addresses fixed-point of a format (ℓ, f) chosen by the circuit; reason: the proof computes ρx + tp in fixed-point form, Eq. (40) and Eq. (42)
--   - generalization: membership queries, unspecified as to control → every oracle call is plain or inverse, with no control wire; reason: the proof uses no controlled query; an uncontrolled circuit is a special case of a circuit with any queries
--   - reading: conditioned data w, p, s, h̃_p(0), then "there is a reversible circuit" → the circuit, its formats and work width chosen after p, s, h̃ and before w, θ; H̃ may depend on w, θ; reason: the circuit sees w and θ only through O_{f_{w,θ}}; §3.1.2 (p. 23) conditions only on s and h̃_p(0) having been obtained
--   - encoding: the value |H̃_p(x)⟩ and grid points x ∈ G_b^n → the Vb value wires read as the offset-binary number fpVal Vb Vf; a basis state of n registers of b qubits is the point (g_b(x_1), …, g_b(x_n)); reason: the proof stores H̃ in reversible fixed-point arithmetic (p. 25, Eq. (42)); g_b is a bijection onto G_b (p. 23)
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.2, p. 23 (PDF p. 24)

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
theorem theorem_3_2 (C₁ C₂ : ℝ) :
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

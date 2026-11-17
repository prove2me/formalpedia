-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_3
-- name    : QuantumLTF.Membership.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:47:40.971078+00:00
-- url     : https://prove2.me/theorems/c131387a-adcf-4bc7-a8fd-ae9f4e2d368e
-- title:
--   Theorem 5.3 — high-degree projection onto the band $B_K$ with $O(K^{1/4}\log(1/\xi))$ uses of $A_w$
-- statement:
--   Let $K\ge1$, $D\ge2K+1$, $M\ge D$, $B_K=\{K,\dots,2K\}$, $p_K=\|\Pi_{B_K}|F_w\rangle\|^2$ and $|F_w^{B_K}\rangle=\Pi_{B_K}|F_w\rangle/\sqrt{p_K}$, and let $0<\xi<1/2$. Suppose $A_w$ is a unitary circuit with
--   $$A_w|0\rangle=\frac1{\sqrt2}\big(|\tilde F_{0,M}\rangle|0\rangle_Y+|\tilde F_{w,M}\rangle|1\rangle_Y\big)\qquad(170)$$
--   and
--   $$\big\|P_D^{\otimes n}|\tilde F_{w,M}\rangle-P_D^{\otimes n}|F_w\rangle\big\|\le\frac{\xi\sqrt{p_K}}4 .\qquad(171)$$
--   Then there is a quantum procedure that, with probability at least $1-\xi^2/16$, prepares a state $|\tilde F^{B_K}_{w,M}\rangle$ with
--   $$\big\||\tilde F^{B_K}_{w,M}\rangle-|F_w^{B_K}\rangle\big\|\le\xi ,$$
--   using $O(K^{1/4}\log(1/\xi))$ applications of $A_w$ and $A_w^\dagger$ and $O(K^{1/4}\log(1/\xi)\,n(\log M+\log(nD)))$ additional elementary gates.
--
--   **Formalization Note** $M=2^q$. The procedure is an oracle circuit calling $A_w$ and $A_w^\dagger$, fixed before $w$ and $A_w$, followed by a measurement of flag qubits. On success the post-measurement state is $\tilde F\otimes\chi$, with $\tilde F$ on the degree registers. $A_w$ may also act on $a$ internal ancillas; $P_D$ then includes $|0\rangle\langle0|_{\mathrm{anc}}$, and the gate bound gains a term $O(K^{1/4}\log(1/\xi)\,a)$.
--
--   Differences from the source:
--   - generalization: A_w on the degree registers and Y, as (170) is printed → A_w on the degree registers, Y and a ≥ 0 internal ancilla qubits; F̃ on registers and ancillas; P_D^{⊗n} includes |0⟩⟨0|_anc; gate bound C K^{1/4} log(1/ξ) (n(log M + log(nD)) + a); reason: a = 0 is exactly the printed statement; for a > 0 it applies to the A_w of Theorem 5.2, whose state has internal ancillas (p. 62), and each reflection about A_w|0⟩ must touch the a extra qubits
--   - reading: a quantum procedure that, with probability at least 1 − ξ²/16, prepares a state F̃ → an oracle circuit over gates12 calling A_w and A_w† (uncontrolled), fixed before w and A_w, followed by a computational-basis measurement of designated flag qubits; the success outcomes have probability ≥ 1 − ξ²/16, and the normalized post-measurement state is F̃ ⊗ χ with F̃ a unit vector on the degree registers and ‖F̃ − F_w^{B_K}‖ ≤ ξ; reason: a heralded preparation; the proof marks the band with Y = 1 by fixed-point amplitude amplification
--   - encoding: M ≥ D; |F_w^{B_K}⟩; O(·) → M = 2^q, D ≤ 2^q; bandKet (degrees in binary, most significant bit first); one constant C fixed before every parameter; reason: same objects; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.3, Eqs. (167)–(171), p. 63 (PDF p. 64)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 5.3 (High-degree projection).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.3, p. 63 (PDF p. 64): "Let `K ≥ 1` and
`D ≥ 2K + 1` … Define `p_K := ‖Π_{B_K}|F_w⟩‖²`, and `|F_w^{B_K}⟩ := Π_{B_K}|F_w⟩/√p_K`. Let
`0 < ξ < 1/2`. Suppose there is a unitary circuit `A_w` satisfying
`A_w|0⟩ = (1/√2)(|F̃_{0,M}⟩|0⟩_Y + |F̃_{w,M}⟩|1⟩_Y)` (170), where the second branch satisfies
`‖P_D^{⊗n}|F̃_{w,M}⟩ − P_D^{⊗n}|F_w⟩‖ ≤ ξ√p_K/4` (171). Then there is a quantum procedure that, with
probability at least `1 − ξ²/16`, prepares a state `|F̃_{w,M}^{B_K}⟩` satisfying
`‖|F̃_{w,M}^{B_K}⟩ − |F_w^{B_K}⟩‖ ≤ ξ`, using `O(K^{1/4} log(1/ξ))` applications of `A_w` and `A_w†`,
together with `O(K^{1/4} log(1/ξ) n (log M + log(nD)))` additional elementary gates."

**Formalization Note.** `M = 2^q ≥ D` (standing assumption, PDF p. 58). `A_w` is any unitary on the
`n` degree registers (wires `0, …, n q − 1`), `Y` (wire `n q`) and `a` internal ancilla wires
(wires `n q + 1, …`), with `A_w|0⟩ = (|F̃_{0,M}⟩|0⟩_Y + |F̃_{w,M}⟩|1⟩_Y)/√2` and `F̃` vectors on the
registers and the ancillas; as on p. 62 (proof of Theorem 5.2), `P_D^{⊗n}` includes `|0⟩⟨0|_anc`
(`projDist`). The printed (170) shows no ancillas: that is the case `a = 0`, where the statement is
exactly the printed one. For `a > 0` the gate bound carries the extra term `C K^{1/4} log(1/ξ) a`
(each reflection about `A_w|0⟩` must touch the `a` wires), which vanishes at `a = 0`. `F̃_{0,M}` and
`F̃_{w,M}` are any vectors with (170) and (171) (no normalization is assumed). The procedure is an
oracle circuit over `gates12` calling `A_w` and `A_w†` (uncontrolled), chosen before `w` and `A_w`
(it may depend on `n, K, D, M, a, ξ`), on `n q + e` wires from `|0…0⟩`, followed by a measurement of
the flag wires `flag` (among the last `e` wires); success is the outcome set `good`. "Prepares a
state `F̃`": on success the normalized post-measurement state is `F̃ ⊗ χ`, `F̃` on the degree registers
(degrees in binary, `bandKet`), `χ` on the other wires. `C` is fixed before all parameters; `log` is
natural. -/
theorem theorem_5_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n K D q a : ℕ) (ξ : ℝ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q → 0 < ξ → ξ < 1 / 2 →
        ∃ (e r : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1 + a) (n * q + e))
          (flag : Fin r ↪ Fin e) (good : Set (Qubits r)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) ∧
          (c.gateCount : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
            (n * (Real.log (2 ^ q) + Real.log (n * D)) + a) ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ A : Matrix (Qubits (n * q + 1 + a)) (Qubits (n * q + 1 + a)) ℂ,
            A ∈ Matrix.unitaryGroup (Qubits (n * q + 1 + a)) ℂ →
          ∀ F0 Fw : EuclideanSpace ℂ (Qubits (n * q + a)),
            (∀ (x : Qubits (n * q)) (y : Bool) (s : Qubits a),
              act A (zeroKet (n * q + 1 + a)) (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) =
                (1 / Real.sqrt 2 : ℂ) * (if y then Fw (Fin.append x s) else F0 (Fin.append x s))) →
            projDist n q a D w Fw ≤ ξ * Real.sqrt (bandWeight w K) / 4 →
            open Classical in
            let ψ := act (c.unitary fun _ => A) (zeroKet (n * q + e))
            let P := probEvent ψ (fun z => (fun j : Fin e => z (Fin.natAdd (n * q) j)) ∘ flag ∈ good)
            1 - ξ ^ 2 / 16 ≤ P ∧
            ∃ (Ft : EuclideanSpace ℂ (Qubits (n * q))) (χ : EuclideanSpace ℂ (Qubits e)),
              ‖Ft‖ = 1 ∧ ‖χ‖ = 1 ∧ ‖Ft - bandKet n q K w‖ ≤ ξ ∧
              ∀ (x : Qubits (n * q)) (s : Qubits e), s ∘ flag ∈ good →
                ψ (Fin.append x s) = (Real.sqrt P : ℂ) * Ft x * χ s := by sorry

end QuantumLTF.Membership.Supplement

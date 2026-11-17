-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_2
-- name    : QuantumLTF.Membership.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:46:56.259125+00:00
-- url     : https://prove2.me/theorems/b98e323e-6d96-4736-996a-e03e6d88f83d
-- title:
--   Theorem 5.2 — finite-dimensional preparation of the Hermite component with one $\mathsf{QEX}_M$ query
-- statement:
--   Let $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$ with $w\in\mathbb S^{n-1}$. Let $D\ge2$ and $0<\eta<1/2$ with $D>\log(4n/\eta)$, and let $M$ be a power of two with
--   $$M\ge\max\Big\{64n^2(D+1),\ \frac{20736\,n^2(D+1)}{\eta^2},\ \frac{165888\,n}{\eta^4},\ \frac4\pi\log\frac{12\sqrt{2n}}{\eta},\ C D^{9/4}\Big(\frac{4n}{\eta}\Big)^{13/4}\Big\},$$
--   where $C>0$ is the universal constant of Lemma 5.2. Then there is a quantum circuit $A_w$, using one query to $\mathsf{QEX}_M(f_w,\gamma_n)$ and $O(n\log^3 M\log(4n/\eta))$ additional elementary gates, such that
--   $$A_w|0\rangle=\frac1{\sqrt2}\big(|\tilde F_{0,M}\rangle|0\rangle_Y+|\tilde F_{w,M}\rangle|1\rangle_Y\big),$$
--   where $|\tilde F_{w,M}\rangle$ is normalized and
--   $$\big\|P_D^{\otimes n}|\tilde F_{w,M}\rangle-P_D^{\otimes n}|F_w\rangle\big\|\le\eta .$$
--
--   **Formalization Note** $M=2^q$. The circuit and $\tilde F_{0,M}$ are fixed before $w$ and the oracle. The states $\tilde F$ live on the $n$ degree registers and $a$ internal ancillas, and $P_D^{\otimes n}$ includes $|0\rangle\langle0|_{\mathrm{anc}}$ (p. 62). $\log$ is natural.
--
--   Differences from the source:
--   - reading: QEX_M(f_w, γ_n) → the published IsQEX: any unitary U on nq + 1 qubits with U|0…0⟩ the discretized Gaussian example state (M = 2^q, label on the last qubit); the statement holds for every such U; reason: QEX_M is a state-preparation oracle (p. 10): only its action on |0⟩ is specified
--   - reading: C > 0 is the universal constant from Lemma 5.2 → ∃ C > 0 (with the gate constant C' > 0) fixed before n, D, η, M; reason: Lemma 5.2 is cited from [JIS+26, Theorem 19] and its constant is not printed
--   - reading: |F̃_{0,M}⟩, |F̃_{w,M}⟩ and P_D^{⊗n} → vectors on the n degree registers and a internal ancilla qubits; P_D^{⊗n} includes |0⟩⟨0|_anc (projDist); F̃_{0,M} chosen before w and U; reason: p. 62: 'P_D denotes P_D ⊗ |0⟩⟨0|_anc'; the name F̃_{0,M} carries no w
--   - encoding: M a power of two ≥ the five-term maximum; one query; O(n log³(M) log(4n/η)) gates → M = 2^q with five separate lower bounds; exactly one plain uncontrolled call; gateCount ≤ C' n (log 2^q)³ log(4n/η); reason: same conditions; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.2, p. 60 (PDF p. 61); proof, p. 61 (PDF p. 62)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

/-- **Theorem 5.2 (Finite-dimensional preparation of the Hermite component).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.2,
p. 60 (PDF p. 61): "Let `f_w(x) = sign(⟨w, x⟩)` with `w ∈ S^{n−1}`. Let `D ≥ 2` and `0 < η < 1/2`
satisfy `D > log(4n/η)`. Let `M` be a power of two satisfying
`M ≥ max{64n²(D+1), 20736 n²(D+1)/η², 165888 n/η⁴, (4/π) log(12√(2n)/η), C D^{9/4} (4n/η)^{13/4}}`,
where `C > 0` is the universal constant from Lemma 5.2. Then there exists a quantum circuit `A_w`,
using one query to `QEX_M(f_w, γ_n)` and `O(n log³(M) log(4n/η))` additional elementary gates, such
that `A_w|0⟩ = (1/√2)(|F̃_{0,M}⟩|0⟩_Y + |F̃_{w,M}⟩|1⟩_Y)`, where `|F̃_{w,M}⟩` is normalized and satisfies
`‖P_D^{⊗n}|F̃_{w,M}⟩ − P_D^{⊗n}|F_w⟩‖ ≤ η`."

**Formalization Note.** `M = 2^q`. `QEX_M(f_w, γ_n)` is the published `IsQEX` (another series):
every unitary `U` on `n q + 1` qubits with `U|0…0⟩` the discretized Gaussian example state on the
lattice `S_Δ[−L, L]`, `Δ = √(4π/M)` (Eq. (149)), label on the last wire; the statement holds for every
such `U`. `C` (Lemma 5.2's constant, "sufficiently large", whose value is not printed) and the gate
constant `C'` are existential and fixed before `n, D, η, M`; the five lower bounds on `M` are the five
terms of the maximum, `log` natural. The circuit `A_w` (over `gates12`, §C.5) is fixed before `w` and
`U`: it has `n q + 1 + a` wires, the `n` degree registers (register `i` on wires `i q, …, i q + q − 1`), the
flag `Y` on wire `n q` and `a` internal ancillas, and makes exactly one plain query (not inverse, not
controlled). `F̃_{0,M}` does not depend on `w`; the states `F̃` live on the registers and the ancillas,
and `P_D^{⊗n}` includes `|0⟩⟨0|_anc` (p. 62), see `projDist` (degrees in binary, most significant bit
first). Every basis string of the `n q + 1 + a` wires is `(r, y, s)` (registers, `Y`, ancillas), so the
displayed identity determines `A_w|0⟩`. -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ (n D : ℕ) (η : ℝ), 2 ≤ D → 0 < η → η < 1 / 2 → Real.log (4 * n / η) < D →
      ∀ q : ℕ,
        64 * (n : ℝ) ^ 2 * (D + 1) ≤ 2 ^ q →
        20736 * (n : ℝ) ^ 2 * (D + 1) / η ^ 2 ≤ 2 ^ q →
        165888 * (n : ℝ) / η ^ 4 ≤ 2 ^ q →
        4 / Real.pi * Real.log (12 * Real.sqrt (2 * n) / η) ≤ 2 ^ q →
        C * (D : ℝ) ^ (9 / 4 : ℝ) * (4 * n / η) ^ (13 / 4 : ℝ) ≤ 2 ^ q →
        ∃ (a : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) (n * q + 1 + a))
          (F0 : EuclideanSpace ℂ (Qubits (n * q + a))),
          Uncontrolled c ∧ ForwardOnly c ∧ c.queryCount 0 = 1 ∧
          (c.gateCount : ℝ) ≤ C' * n * Real.log (2 ^ q) ^ 3 * Real.log (4 * n / η) ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ U : Matrix (Qubits (n * q + 1)) (Qubits (n * q + 1)) ℂ, IsQEX (q := q) w U →
            ∃ Fw : EuclideanSpace ℂ (Qubits (n * q + a)), ‖Fw‖ = 1 ∧
              (∀ (r : Qubits (n * q)) (y : Bool) (s : Qubits a),
                act (c.unitary fun _ => U) (zeroKet (n * q + 1 + a))
                    (Fin.append (Fin.snoc (α := fun _ => Bool) r y) s) =
                  (1 / Real.sqrt 2 : ℂ) *
                    (if y then Fw (Fin.append r s) else F0 (Fin.append r s))) ∧
              projDist n q a D w Fw ≤ η := by sorry

end QuantumLTF.Membership.Supplement

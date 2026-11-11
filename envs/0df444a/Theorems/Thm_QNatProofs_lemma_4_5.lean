-- Prove2me | Theorems.Thm_QNatProofs_lemma_4_5
-- name    : QNatProofs.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:34.482688+00:00
-- url     : https://prove2.me/theorems/39643dbd-e8e0-4679-9a51-bba4c7f4bc37
-- title:
--   Lemma 4.5 — amplitude loading for one trial
-- statement:
--   There is an absolute constant $c$, and for every QNC$^0$ depth $D$ a depth $D'$, with the following property. For all $n,q,j$ there is an oracle template $T$ on $n+(2q+j)+e$ wires that makes exactly one call to $U$ and one call to $U^\dagger$, has at most $c(n+q^2\log(q+1))$ other gates, and uses $e\le c\,q^2$ additional ancillas, such that: for every even $\sigma\ge2$, every $\gamma\in(0,1]$, every vector $v$ of $q$-bit polar amplitudes with $\|v\|\ge\gamma\sqrt N$, and every amplitude oracle $U_v$ in $A_\sigma CQ$ (depth $D$) acting on $n+2q+j$ wires, some circuit $C\in A_{2\sigma+2}CQ$ (depth $D'$) implements $T$ with $U_v$ and prepares
--   $$
--   |\hat v\rangle=\frac1{\|v\|}\sum_xv_x|x\rangle\quad\text{with probability}\quad p=\frac{\|v\|^2}{2^n(1-2^{-q'})^2}\ge\gamma^2 ,
--   $$
--   where $q'=2^{\lceil\log_2q\rceil}$ is $q$ padded to a power of two ($q'=q$ when $q$ is a power of two).
--
--   This is the single LCU trial that Lemma 4.6 repeats in parallel.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: A_σCQ, A_{2σ+2}CQ with constant depth; O(·) → MHLevel σ D and MHLevel (2σ+2) D', D' depending only on D; one absolute c; reason: constant depth is fixed before the size parameters
--   - reading: This circuit uses one call each to U_v and U_v†, together with O(n + q² log(q+1)) additional gates and O(q²) additional ancilla qubits → a template T with exactly one uncontrolled call to U and one to U† (IsCallTemplate T 1), chosen before v and U, gateCount T ≤ c(n + q² log(q+1)), e ≤ c q² extra wires; C has the unitary of T with U substituted and no more gates (ImplementsTemplate); reason: the call structure must be explicit; C may merge the template's gates into U's blocks, which is how the level 2σ + 2 is reached (p.27–28)
--   - reading: p = ‖v‖²/(2ⁿ(1 − 2^{−q})²) → p = ‖v‖²/(2ⁿ(1 − 2^{−q'})²) with q' = 2^{⌈log₂ q⌉}; reason: the proof takes q to be a power of two, 'Otherwise, pad the magnitude encoding with trailing zeros … and redefine q to be this padded length' (p.26); the two coincide when q is a power of two
--   - encoding: prepares |v̂⟩ with probability p → PreparesWithProb: on a computational-basis success event of the non-output wires the state is |v̂⟩ ⊗ |φ⟩ with ‖φ‖² = p; reason: the success branch J = 0, B = 1 of the proof is such an event
--   - encoding: amplitude oracle U_v|x⟩|0⟩ = |x⟩|r_x⟩|θ_x⟩|junk_x⟩ → IsAmplitudeOracle on wires x, r_x, θ_x, workspace; output register the first n wires; reason: a renaming of wires
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.5, p.26; proof p.26–28; Definition 4.1 (γ ∈ (0,1]), p.26

import Mathlib
import Definitions.Def_QNatProofs_IsAmplitudeOracle

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- **Lemma 4.5 (Amplitude loading for one trial)** (Li, Parham, *Natural proofs for quantum state
preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.26; proof p.26–28):
"Suppose we have access to an amplitude oracle `U_v` and its inverse, outputting `r_x` and `θ_x` on
`q` qubits, with `U_v, U_v† ∈ A_σCQ` for even `σ ≥ 2`. Assume `‖v‖ ≥ γ√N`. Then there exists a
circuit in `A_{2σ+2}CQ` that prepares `|v̂⟩ = (1/‖v‖) Σ_x v_x |x⟩` with probability
`p = ‖v‖²/(2ⁿ(1−2^{-q})²) ≥ γ²`. This circuit uses one call each to `U_v` and `U_v†`, together with
`O(n + q² log(q + 1))` additional gates and `O(q²) additional ancilla qubits`." Here `γ ∈ (0, 1]` is
the balance parameter fixed in Definition 4.1 (p.26).

**Formalization Note** `A_kCQ` is `MHLevel k D`; the depth `D'` of the output circuit depends only
on the depth `D` of the oracle circuit, and the constant `c` of both `O(·)` is absolute. "One call
each" is a template `T` (an oracle circuit with exactly one uncontrolled call to `U` and one to `U†`
and at most `c(n + q² log(q+1))` elementary gates) chosen before `v` and `U`; the circuit `C`
implements `T` with `U` substituted (same unitary, no more gates), and lies in level `2σ + 2`.
The amplitude oracle acts on the first `n + 2q + j` wires; the `e ≤ c q²` further wires are the
additional ancillas. Success is a computational-basis event on the non-output wires. As in the
proof (p.26), `q` is padded to the next power of two `q' = 2^{⌈log₂ q⌉}`, and the success
probability is `‖v‖²/(2ⁿ(1−2^{-q'})²)` (equal to the printed formula when `q` is a power of two). -/
theorem lemma_4_5 : ∃ c : ℝ, ∀ D : ℕ, ∃ D' : ℕ, ∀ n q j : ℕ, ∃ (e : ℕ)
    (T : OracleCircuit allGates (fun _ : Fin 1 => n + (q + q + j)) (n + ((q + q + j) + e))),
    IsCallTemplate T 1 ∧
    (T.gateCount : ℝ) ≤ c * ((n : ℝ) + (q : ℝ) ^ 2 * Real.log ((q : ℝ) + 1)) ∧
    (e : ℝ) ≤ c * (q : ℝ) ^ 2 ∧
    ∀ σ : ℕ, Even σ → 2 ≤ σ → ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∀ rb θb : Qubits n → Fin q → Bool,
      γ * Real.sqrt ((2 : ℝ) ^ n) ≤ ‖ampVec (ampOf rb θb)‖ →
    ∀ U : Circuit allGates (n + (q + q + j)), U ∈ MHLevel σ D _ →
      IsAmplitudeOracle U.unitary rb θb →
    ∃ C : Circuit allGates (n + ((q + q + j) + e)), C ∈ MHLevel (2 * σ + 2) D' _ ∧
      ImplementsTemplate C T U ∧
      PreparesWithProb C (vHat (ampOf rb θb))
        (‖ampVec (ampOf rb θb)‖ ^ 2 /
          ((2 : ℝ) ^ n * (1 - (2 : ℝ)⁻¹ ^ (2 ^ Nat.clog 2 q)) ^ 2)) ∧
      γ ^ 2 ≤ ‖ampVec (ampOf rb θb)‖ ^ 2 /
          ((2 : ℝ) ^ n * (1 - (2 : ℝ)⁻¹ ^ (2 ^ Nat.clog 2 q)) ^ 2) := by sorry

end QNatProofs

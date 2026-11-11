-- Prove2me | Theorems.Thm_QNatProofs_lemma_4_6
-- name    : QNatProofs.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:51.001387+00:00
-- url     : https://prove2.me/theorems/93b71e02-b63f-499b-bde4-e033eb634b42
-- title:
--   Lemma 4.6 — amplitude loading in MH
-- statement:
--   There is an absolute constant $c$, and for every QNC$^0$ depth $D$ a depth $D'$, with the following property. Let $n,q,j\in\mathbb N$, $\gamma\in(0,1]$, $\delta_{\mathrm{load}}\in(0,1)$, and $t=\lceil\gamma^{-2}\ln(1/\delta_{\mathrm{load}})\rceil$. There is an oracle template $T$ with exactly $t$ calls each to $U$ and $U^\dagger$, at most $c(tq^2\log(q+1)+t^2\log(t+1)+nt)$ other gates and $e\le c(tq^2+t^2\log(t+1)+nt)$ additional ancillas, such that for every even $\sigma\ge10$, every vector $v$ of $q$-bit polar amplitudes with $\|v\|\ge\gamma\sqrt N$, and every amplitude oracle $U_v$ in $A_\sigma CQ$ (depth $D$), some amplitude loader $C\in A_{2\sigma+4}CQ$ (depth $D'$) implements $T$ with $U_v$ and its reduced output state $\rho_v$ satisfies
--   $$
--   \tfrac12\big\|\rho_v-|\hat v\rangle\langle\hat v|\big\|_1\le\delta_{\mathrm{load}}.\tag{51}
--   $$
--
--   This is the amplitude loader used for the PRAL states in Corollary 4.6.1.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: A_σCQ, A_{2σ+4}CQ with constant depth; O(·) → MHLevel σ D and MHLevel (2σ+4) D', D' depending only on D; one absolute c; reason: constant depth is fixed before the size parameters
--   - reading: t parallel calls each to U_v and U_v†, together with O(tq² log(q+1) + t² log(t+1) + nt) additional gates and O(tq² + t² log(t+1) + nt) additional ancilla qubits → a template T with exactly t uncontrolled calls to U and t to U† (IsCallTemplate T t), chosen before v and U, with the two bounds; C implements T (same unitary, no more gates); the parallelism is what the level 2σ + 4 of C certifies; reason: the call structure must be explicit; t sequential calls would need level about tσ
--   - encoding: assume max_x |v_x| ≤ 1 → not a hypothesis; reason: v_x = r_x e^{2πiθ_x} with a q-bit fraction r_x < 1, so the bound always holds
--   - encoding: a designated n-qubit output register; the other qubits traced out → the first n wires; the partial trace over the remaining wires (reducedOutput); reason: any designation is a renaming of wires, which changes neither size nor level
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.6, (51), p.30; proof p.30–32

import Mathlib
import Definitions.Def_QNatProofs_IsAmplitudeOracle

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- **Lemma 4.6 (Amplitude loading in MH)** (Li, Parham, *Natural proofs for quantum state
preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.30; proof p.30–32):
"Suppose we are given access to an amplitude oracle `U_v` for `v = (v_x)_{x∈{0,1}ⁿ}` and its inverse
`U_v†`, where `U_v, U_v† ∈ A_σCQ` for even `σ ≥ 10`. Assume that `max_x |v_x| ≤ 1` and `‖v‖ ≥ γ√N`
for some balance parameter `γ ∈ (0, 1]`, and define `|v̂⟩ = (1/‖v‖) Σ_x v_x |x⟩`. For any error
parameter `δ_load ∈ (0, 1)`, there exists an amplitude loader in `A_{2σ+4}CQ` whose reduced output
state `ρ_v` satisfies `(1/2)‖ρ_v − |v̂⟩⟨v̂|‖₁ ≤ δ_load`. (51) The construction uses
`t = ⌈γ^{-2} ln(1/δ_load)⌉` parallel repetitions of the single trial from Lemma 4.5, and hence `t`
parallel calls each to `U_v` and `U_v†`, together with `O(tq² log(q + 1) + t² log(t + 1) + nt)`
additional gates and `O(tq² + t² log(t + 1) + nt)` additional ancilla qubits."

**Formalization Note** `A_kCQ` is `MHLevel k D`; `D'` depends only on `D`, and the constant `c` of
the `O(·)` bounds is absolute. The call structure is a template `T` with exactly `t` uncontrolled
calls to `U` and `t` to `U†` (`t = loadReps γ δ_load`), chosen before `v` and `U`; the loader `C`
implements `T` with `U` substituted (same unitary, no more gates) and lies in level `2σ + 4`, which
is where the parallelism of the calls is used. The output register is the first `n` wires; then come
`t` oracle registers of `n + 2q + j` wires each, and `e` additional ancillas. The hypothesis
`max_x |v_x| ≤ 1` holds automatically, since `v_x = r_x e^{2πiθ_x}` with a `q`-bit fraction
`r_x < 1`. -/
theorem lemma_4_6 : ∃ c : ℝ, ∀ D : ℕ, ∃ D' : ℕ, ∀ (n q j : ℕ) (γ δ : ℝ), 0 < γ → γ ≤ 1 →
    0 < δ → δ < 1 →
    ∃ (e : ℕ) (T : OracleCircuit allGates (fun _ : Fin 1 => n + (q + q + j))
        (n + (loadReps γ δ * (n + (q + q + j)) + e))),
      IsCallTemplate T (loadReps γ δ) ∧
      (T.gateCount : ℝ) ≤ c * ((loadReps γ δ : ℝ) * (q : ℝ) ^ 2 * Real.log ((q : ℝ) + 1) +
        (loadReps γ δ : ℝ) ^ 2 * Real.log ((loadReps γ δ : ℝ) + 1) + (n : ℝ) * loadReps γ δ) ∧
      (e : ℝ) ≤ c * ((loadReps γ δ : ℝ) * (q : ℝ) ^ 2 +
        (loadReps γ δ : ℝ) ^ 2 * Real.log ((loadReps γ δ : ℝ) + 1) + (n : ℝ) * loadReps γ δ) ∧
      ∀ σ : ℕ, Even σ → 10 ≤ σ →
      ∀ rb θb : Qubits n → Fin q → Bool,
        γ * Real.sqrt ((2 : ℝ) ^ n) ≤ ‖ampVec (ampOf rb θb)‖ →
      ∀ U : Circuit allGates (n + (q + q + j)), U ∈ MHLevel σ D _ →
        IsAmplitudeOracle U.unitary rb θb →
      ∃ C : Circuit allGates (n + (loadReps γ δ * (n + (q + q + j)) + e)),
        C ∈ MHLevel (2 * σ + 4) D' _ ∧ ImplementsTemplate C T U ∧
        ApproxPrepares C (vHat (ampOf rb θb)) δ := by sorry

end QNatProofs

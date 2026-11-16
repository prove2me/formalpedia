-- Prove2me | Theorems.Thm_QubitFreqSensing_Supplement_theorem_8_1
-- name    : QubitFreqSensing.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:59:51.981409+00:00
-- url     : https://prove2.me/theorems/1dccb839-c57a-4ee1-a16a-24d62c0162db
-- title:
--   Theorem 8.1 — discrete Grover–Heisenberg limit $T\ge\frac{1}{6\sqrt{30}\,e}\cdot\frac{\sqrt m}{B}$ for $B$-separated frequencies, any ancillas, known phase
-- statement:
--   Let $B>0$ and let $\omega_1,\dots,\omega_m>0$ be pairwise separated, $|\omega_i-\omega_j|\ge B$ for $i\ne j$. Fix a phase $\phi\in\mathbb R$, known to the protocol. Consider any purified sensing protocol on the sensing qubit and an arbitrary finite auxiliary register (initial unit vector $v$, measurable control-only unitary evolution $U_c$ with $U_c(0)=I$, final effect $0\le E\le I$) that runs for total time $T\ge0$, all waits and repetitions included. For each $j$ let $c_j$ be its coefficient vector under the signal Hamiltonian $H_j(t)=B\cos(\omega_j t+\phi)\,(Z\otimes I)$ on $[0,T]$. Suppose the protocol distinguishes the zero Hamiltonian from every $H_j$ with error probability at most $1/3$:
--
--   1. with no signal it reports "signal" with probability $\langle U_c(T)v,\,E\,U_c(T)v\rangle\le 1/3$;
--   2. under each $H_j$ it reports "signal" with probability $\langle U_c(T)c_j(T),\,E\,U_c(T)c_j(T)\rangle\ge 2/3$.
--
--   Then
--
--   $$
--   T\ \ge\ \frac{1}{6\sqrt{30}\,e}\cdot\frac{\sqrt m}{B}. \tag{22}
--   $$
--
--   This is the discrete Grover–Heisenberg limit: for the frequencies $\omega_j=jB$ it shows that the $O(\sqrt N/B_{\min}+1/\omega_{\min})$ sensing time of the mission's single-qubit protocol (Theorem 1.1) is optimal up to constants in the worst case, even against protocols with arbitrarily many auxiliary qubits, arbitrary controls, and a known phase.
--
--   Differences from the source:
--   - generalization: the bound holds even if the phase is known to be ϕ = 0 (the error hypothesis at ϕ = 0 only) → one known phase ϕ ∈ ℝ, the same for every i, with the error hypotheses only at that ϕ; reason: at ϕ = 0 this is exactly the page's strongest form, and it implies the version where the protocol must succeed for every ϕ; the page's Fourier bound (Lemma 8.2, cosine version) holds verbatim for cos(λs + ϕ)
--   - generalization: arbitrarily many auxiliary qubits → an arbitrary finite auxiliary register α (any dimension, not only powers of 2); reason: k auxiliary qubits are α = Fin (2^k)
--   - generalization: any protocol (controls, waits, repetitions, measurements), purified as on p.31 → every purified protocol with an entrywise measurable unitary control path U_c, U_c(0) = I, initial unit vector v and final effect 0 ≤ E ≤ I; reason: the page's purification maps every protocol into this class; measurable paths include every physical control and instantaneous gates
--   - encoding: error probability at most 1/3 on every such Hamiltonian, the zero one included → P(signal | H ≡ 0) ≤ 1/3 and P(signal | H_j) ≥ 2/3 for every j; reason: the two-outcome form of error ≤ 1/3 on each Hamiltonian
--   - encoding: evolution under B cos(ω_j t + ϕ)(Z ⊗ I), eq. (29) → c_j continuous on [0, T] with c_j(t) = v − i ∫₀ᵗ B cos(ω_j s + ϕ) M(s) c_j(s) ds; with no signal c ≡ v; reason: the integral form of (6)/(29); the solution exists and is unique
--   - encoding: the protocol finishes within time T → final measurement at absolute time T ≥ 0; reason: a protocol that finishes at T′ ≤ T satisfies the bound at T′, hence at T
--   - encoding: e → Real.exp 1; ω_1, …, ω_m indexed by Fin m; reason: Lean conventions
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Theorem 8.1, eq. (22), p.26 (PDF p.26); proof, pp.31–32; informal form Theorem 1.2, p.4

import Mathlib
import Definitions.Def_QubitFreqSensing_Supplement_PurifiedProtocol

open Matrix

namespace QubitFreqSensing.Supplement

/-- **Theorem 8.1 (discrete-frequency sensing lower bound)** (Chen, Coladangelo, Li, Zhang,
*Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit*, manuscript
(STOC 2027 submission), Theorem 8.1, p.26; informal form Theorem 1.2, p.4). "Let B > 0 and let
ω1, . . . , ωm > 0 satisfy |ωi − ωj| ≥ B (i ≠ j). Consider a protocol that distinguishes the zero
Hamiltonian from each of the signal Hamiltonians Hsig(t) = B cos(ωit + ϕ)Z, i ∈ {1, . . . , m}, with
error probability at most 1/3 on every such Hamiltonian. Suppose the protocol, including all waits
and repetitions, finishes within time T. Then, T ≥ (1/(6√30 e)) · √m/B. (22) The bound holds even
if the phase is known to be ϕ = 0, and even with arbitrarily many auxiliary qubits."

**Formalization Note** The protocol is any purified protocol (`PurifiedProtocol`) on the sensing
qubit and an arbitrary finite auxiliary register `α`, run for total time `T ≥ 0` (absolute time,
all waits and repetitions included). The phase `ϕ` is one known real number, the same for all `i`;
the error hypotheses are required only at that `ϕ` (with `ϕ = 0` this is the page's "phase known to
be `ϕ = 0`" form, the strongest). `c j` is the coefficient vector under `B cos(ω_j t + ϕ)(Z ⊗ I)`;
with no signal it is the constant `v = P.init`. Error at most `1/3` on every Hamiltonian:
`P(signal | H ≡ 0) ≤ 1/3` and `P(signal | ω_j) ≥ 2/3` for every `j`. `e = Real.exp 1`. -/
theorem theorem_8_1 (B : ℝ) (hB : 0 < B) (m : ℕ) (ω : Fin m → ℝ) (hω : ∀ i, 0 < ω i)
    (hsep : ∀ i j, i ≠ j → B ≤ |ω i - ω j|) (ϕ : ℝ)
    (α : Type) [Fintype α] [DecidableEq α] (P : PurifiedProtocol α) (T : ℝ) (hT : 0 ≤ T)
    (c : Fin m → ℝ → Fin 2 × α → ℂ)
    (hc : ∀ j, P.IsCoeffSolution (fun t => B * Real.cos (ω j * t + ϕ)) T (c j))
    (hzero : P.probSignal ((P.control T : Matrix (Fin 2 × α) (Fin 2 × α) ℂ) *ᵥ P.init) ≤ 1 / 3)
    (hsig : ∀ j, 2 / 3 ≤ P.probSignal ((P.control T : Matrix (Fin 2 × α) (Fin 2 × α) ℂ) *ᵥ c j T)) :
    1 / (6 * Real.sqrt 30 * Real.exp 1) * (Real.sqrt m / B) ≤ T := by sorry

end QubitFreqSensing.Supplement

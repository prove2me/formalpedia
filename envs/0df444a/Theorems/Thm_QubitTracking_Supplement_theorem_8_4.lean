-- Prove2me | Theorems.Thm_QubitTracking_Supplement_theorem_8_4
-- name    : QubitTracking.Supplement.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:15:40.959271+00:00
-- url     : https://prove2.me/theorems/b9a56292-6fca-4297-8322-8c8433f4a61e
-- title:
--   Theorem 8.4 (NDEL security, warmup version) — two-round entanglement localization is non-destructive, 1-complete, and extracts EPR pairs with fidelity $1-O(\eta^{1/4})-\mathsf{negl}$
-- statement:
--   **Theorem 8.4 (NDEL security, warmup version).** Construction 8.3 is a non-destructive entanglement localization scheme with $1$-Completeness and $(\beta,\Delta)$-Extraction Soundness, where
--   $$\beta(\lambda,\eta)=1-O\big(\eta(\lambda)^{1/4}\big)-\mathsf{negl}(\lambda).$$
--
--   In Construction 8.3 the setup hands the prover the vessel $\mathbf B$ of the anchor state $|\Psi^{\mathsf{sk}}\rangle_{\mathbf{AB}}$ and publishes the oracles $\mathcal O_{\mathrm{Chal}}$ and $\mathcal O$; for $i=0,1$ the verifiers at $-1$ and $1$ send secret shares $x_{L,i},x_{R,i}$ that meet at $L$ at time $t+i\Delta/2$, and accept iff both responses equal $\mathcal O(\theta_i,x_{L,i}\oplus x_{R,i},w_i)$ with $\theta_i=\mathcal O_{\mathrm{Chal}}(x_{L,i}\oplus x_{R,i})$, $w_i=v$ if $\theta_i=0$ and $w_i=u$ if $\theta_i=1$. Precisely, the theorem asserts:
--
--   1. **Completeness and non-destructiveness.** For all parameters ($n(\lambda),m(\lambda)\ge\lambda$ polynomially bounded, $\Delta(\lambda)>0$) and every claimed point $(L,t)$ with $L\in[-1,1]$, there is a QPT prover family at position $L$ that is accepted with probability $1$ at every $\lambda$, and whose expected trace distance between the setup state on $\mathbf{AB}$ and the state on $\mathbf{AB}'$ after $\mathsf{Localize}$ is bounded by a negligible function.
--   2. **Extraction soundness.** There is a universal constant $C>0$ such that for all parameters, every claimed point $(L,t)$ and every QPT prover family $\mathcal P^*$ with failure probability $\eta(\lambda)=1-\Pr[b=\top]$, there is a negligible $\nu$ such that at every $\lambda$ some (unbounded) channel acting on $\mathsf{register}[[L-\Delta,L+\Delta]@t]$, given the public parameters, outputs $n$ qubits whose expected fidelity with $|\mathsf{EPR}\rangle^{\otimes n}$ (shared with the anchor $\mathbf A$) is at least
--   $$1-C\,\eta(\lambda)^{1/4}-\nu(\lambda).$$
--
--   This is the two-round warm-up whose spacetime chunking proof is reused by Theorems 9.3 and 9.6; unlike them it controls the expected fidelity directly in terms of the failure probability.
--
--   **Formalization Note** Construction 8.3 is the published protocol of Construction 9.5 with the two-round schedule `sched83`; the base mission's `Prover95`, `accProb95` and `ExtractsAt95` are used with the constant trajectory $L$. The extraction event with success probability $1$ forces the extractor to be a channel on the states that occur.
--
--   Differences from the source:
--   - reading: time t ∈ ℝ≥0 (§3.2, p.21) → time is ℝ; reason: Constructions 8.3/9.2/9.8 broadcast at t + iδ − (L + 1), which is negative for small t; positions stay in [−1, 1] (base mission D2)
--   - reading: a prover in spacetime: cells moving at most at the speed of light, circuits at intersection points (§3.2, pp.21–23) → the published QubitTracking.Prover / Prover.Valid: finitely many one-qubit cells with 1-Lipschitz trajectories in [−1, 1], a time-sorted list of located one-qubit, two-qubit and oracle-query gates acting only on colocated cells, designated input, challenge and response cells; reason: the paper's model is prose; this is the published pinned-down model of the live mission (base D4)
--   - generalization: QPT: polynomially many gates from a fixed universal gate set (p.22) → IsQPT: polynomially many gates, each an arbitrary one-qubit unitary, two-qubit unitary or oracle query; non-uniform families; reason: every circuit over a fixed universal gate set of one- and two-qubit gates is such a circuit of the same size, so the soundness clause covers every QPT prover of the paper (base D5)
--   - encoding: the oracle output in 𝔽₂^m ∪ {⊥} → m + 1 qubits, y ↦ (y, 0), ⊥ ↦ (0^m, 1) (encOpt), queried by the standard XOR unitary; reason: a fixed injective encoding (base D6)
--   - encoding: classical challenges broadcast at the send time; responses received at the deadline → challenge cells start in the basis state of the challenge; responses are measured in the computational basis at the end of the run; reason: no gate may touch a challenge cell before its broadcast time or a response cell after its deadline, so both are the same experiment (base D7)
--   - reading: register[L_Δ @ t] (Definition 3.2) → the reduced state on the cells located in [L − Δ, L + Δ] at time t, excluding challenge cells not yet broadcast and response cells already received, with the heard transcripts of 𝒱_L and 𝒱_R as classical side information (regionMem, regState, heardTranscript); reason: items 1–3 of Definition 3.2 (base D8)
--   - reading: O(·) and negl(λ) in β → ∃ C > 0 before every parameter (n, m, Δ, γ, L, t, the prover); a negligible ν (PPADSIS.SubexpSIS.Negligible) chosen after the prover; the bound holds at every λ; reason: the O-constant of Theorem 7.9 is universal; the negligible term depends on the prover (base D11)
--   - reading: n(λ), m(λ) ≥ λ polynomials → n, m : ℕ → ℕ polynomially bounded (PolyBounded) with λ ≤ n(λ), λ ≤ m(λ); reason: the construction's parameter clause
--   - reading: the claimed point (L, t) → L ∈ [−1, 1] and t ∈ ℝ fixed, independent of λ, quantified before the prover; reason: "For any L, t and QPT prover 𝒫*, let η(λ) := …" fixes (L, t) before the function η(λ)
--   - reading: a QPT prover 𝒫 at position (L, t) (α-Completeness); the honest prover holds 𝐁 at location L → IsAtPoint: every gate of the prover is located at L and its input cells stay at L at all times; the prover family is QPT; reason: the honest prover of the construction "consists of a single party always holding the 𝐁 register at location L"
--   - reading: non-destructive: 𝔼[TD(ρ, ρ′)] ≤ negl(λ) for the prover 𝒫 of completeness → the same prover family that is accepted with probability 1 has per-sample trace distance TD = ½‖ρ − ρ′‖₁ (WildeQIT.traceDist) between the setup state and the reduced state of the prover's input cells after the run, averaged over all randomness, bounded by a negligible function at every λ; reason: the definition's 𝒫 is the completeness prover; the prover's output register 𝐁′ is its input cells after Localize
--   - reading: S, T, u, v of the setup → the anchor data of Definition 4.2 with n_e = n_h = n_s = n: U_shift uniform in GL_{3n}(𝔽₂), u = U_shift^{−t}(u′ × 0), v = U_shift(0 × v′) for uniform u′, v′ (anchorS, anchorT, anchorU, anchorV); reason: the anchor state is generated by GenAnchorState (Definition 4.2), whose data determine S, T, u, v; Fact 4.5 uses the cosets T + v and S^⊥ + u (base D15, D17)
--   - reading: Construction 8.3's oracles, anchor state and acceptance test → the published protocol of Construction 9.5 (Prover95, initState95, Accepts95, accProb95) with the two-round schedule sched83 (δ = Δ/2, rounds at t and t + Δ/2); reason: Construction 8.3 is literally Construction 9.5's setup, oracles and acceptance test with this schedule; θ_i = 𝒪_Chal(x_{L,i} ⊕ x_{R,i})
--   - reading: "Take some localization parameter Δ(λ)" → Δ(λ) > 0, no upper bound; reason: a localization parameter is positive; Construction 8.3 states no upper bound, so none is imposed
--   - reading: 1 − η(λ) := Pr[b = ⊤]; 𝔼[⟨EPR|^{⊗n} ρ_{𝐀𝐁*} |EPR⟩^{⊗n}] ≥ β(λ, η) for a (potentially unbounded) extractor ℰ(pp, 𝐁*) → η = 1 − accProb95; ExtractsAt95 with success probability 1: an extractor reading pp and the heard transcripts, a finite Kraus family on the region's cells with Tr ρ̂ ≥ 1, i.e. a channel, and ⟨EPR^{⊗n}|ρ̂|EPR^{⊗n}⟩ ≥ β · Tr ρ̂ = β; reason: Definition 8.1's extractor is a channel and its guarantee an expected fidelity; a trace-non-increasing family with average trace ≥ 1 is trace preserving on the states that occur
--   - encoding: β(λ, η) = 1 − O(η(λ)^{1/4}) − negl(λ) → 1 − C · (1 − accProb95)^{(1/4 : ℝ)} − ν(λ); reason: real power of the failure probability, which lies in [0, 1]
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 8.4, p.58, with Definition 8.1, pp.56–57, and Construction 8.3, pp.57–58

import Definitions.Def_QubitTracking_Supplement_sched92
import Definitions.Def_QubitTracking_Supplement_ndDist95

set_option autoImplicit false

namespace QubitTracking.Supplement

/-- **Theorem 8.4 (NDEL security, warmup version)** (Bartusek, Huang, Orshansky, Yuen, *How To
Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat)*, arXiv:2605.30732 (held
version, sha256 bf98e5b5…), Theorem 8.4, p.58, with Definition 8.1, pp.56–57, and Construction 8.3,
p.57; pinned down in the model of the base mission). Construction 8.3 is a non-destructive
entanglement localization scheme with 1-Completeness and `(β, Δ)`-Extraction Soundness,
`β(λ, η) = 1 − O(η(λ)^{1/4}) − negl(λ)`.

The clauses:
1. *1-Completeness and non-destructiveness*: for every claimed point `(L, t)` there is a QPT prover
   family at position `L` that is accepted with probability `1` at every `λ`, and whose expected
   trace distance between the setup state on `𝐀𝐁` and the state on `𝐀𝐁′` after `Localize` is
   bounded by a negligible function.
2. *Extraction soundness*: a universal constant `C > 0` such that for all parameters, every claimed
   point `(L, t)` and every QPT prover family `P*` with failure probability
   `η(λ) = 1 − accProb`, there is a negligible `ν` such that at every `λ` a local extractor on
   `register[[L − Δ, L + Δ] @ t]` (a channel: success probability `1`) has expected fidelity
   `≥ 1 − C·η(λ)^{1/4} − ν(λ)` with `n` EPR pairs.

**Formalization Note** Construction 8.3 is Construction 9.5's protocol (setup, oracles, acceptance)
with the two-round schedule `sched83`; the base mission's `Prover95`, `accProb95` and
`ExtractsAt95` are reused with the constant trajectory `fun _ => L`. -/
theorem theorem_8_4 :
    (∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ), Params84 n m Δ →
      ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
        ∃ P : (l : ℕ) → Prover95 (n l) (m l) l (sched83 L t (Δ l)),
          IsQPT P ∧ (∀ l, IsAtPoint (P l) L) ∧ (∀ l, accProb95 (P l) = 1) ∧
            ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧ ∀ l, ndDist95 (P l) ≤ ν l) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ), Params84 n m Δ →
        ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
          ∀ P : (l : ℕ) → Prover95 (n l) (m l) l (sched83 L t (Δ l)), IsQPT P →
            ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
              ∀ l, ExtractsAt95 (P l) (fun _ => L) (Δ l) t 1
                (1 - C * (1 - accProb95 (P l)) ^ (1 / 4 : ℝ) - ν l)) := by sorry

end QubitTracking.Supplement

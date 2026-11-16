-- Prove2me | Theorems.Thm_QubitTracking_Supplement_theorem_9_3
-- name    : QubitTracking.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:16:17.71352+00:00
-- url     : https://prove2.me/theorems/b32654ca-bbbf-4498-b40c-cc9c536feb84
-- title:
--   Theorem 9.3 — entanglement localization at a point: non-destructive, 1-complete, extraction with probability $\eta$ and fidelity $1-O((\log(1/\eta)/\gamma)^{1/4})-\mathsf{negl}$
-- statement:
--   **Theorem 9.3.** Construction 9.2 is a non-destructive entanglement localization scheme for the state $\sigma=|\mathsf{EPR}\rangle\langle\mathsf{EPR}|^{\otimes n}$ in the classical oracle model with $1$-Completeness and $(\beta,\beta',\Delta)$-Extraction Soundness, where
--   $$\beta(\lambda,\eta)=1-O\Big(\Big(\frac{\log(1/\eta)}{\gamma}\Big)^{1/4}\Big)-\mathsf{negl}(\lambda),\qquad\beta'(\lambda,\eta)=\eta(\lambda).$$
--   In particular, for any polynomial $q(\lambda)$, setting $\gamma=c\lambda q^4$ for some constant $c$ achieves $\beta(\lambda,\eta)\ge1-1/q(\lambda)$.
--
--   Construction 9.2 repeats the two-round test of Construction 8.3 at $\gamma+1$ checkpoints $t_i=t+i\delta$, $\delta=\Delta/(\gamma+2)$, $i=0,\dots,\gamma$, with the same anchor state, oracles and acceptance test. Precisely, the theorem asserts:
--
--   1. **Completeness and non-destructiveness.** For all parameters ($n(\lambda),m(\lambda)\ge\lambda$ polynomially bounded, $0<\Delta(\lambda)\le1$, a polynomially bounded repetition factor $\gamma(\lambda)\ge1$) and every claimed point $(L,t)$ with $L\in[-1,1]$, there is a QPT prover family at position $L$, accepted with probability $1$ at every $\lambda$, whose expected trace distance between the setup state on $\mathbf{AB}$ and the state on $\mathbf{AB}'$ after $\mathsf{Localize}$ is negligible.
--   2. **Extraction soundness.** There is a universal constant $C>0$ such that for all parameters, every claimed point $(L,t)$ and every QPT prover family $\mathcal P^*$ with acceptance probability $\eta(\lambda)\ge1/p(\lambda)$ for a polynomial $p$, there is a negligible $\nu$ such that at every $\lambda$ a local extractor on $\mathsf{register}[[L-\Delta,L+\Delta]@t]$ succeeds with probability at least $\eta(\lambda)$ and, conditioned on success, has fidelity with $|\mathsf{EPR}\rangle^{\otimes n}$ (shared with the anchor) at least
--   $$1-C\Big(\frac{\log(1/\eta(\lambda))}{\gamma(\lambda)}\Big)^{1/4}-\nu(\lambda).$$
--   3. **In particular.** For every polynomial $q\ge1$ there is $c>0$ such that with $\gamma(\lambda)=\max(1,\lceil c\lambda q(\lambda)^4\rceil)$, every such prover admits, for all sufficiently large $\lambda$, a local extractor with success probability at least $\eta(\lambda)$ and conditional fidelity at least $1-1/q(\lambda)$.
--
--   This is the stationary counterpart of trajectory verification (Theorem 9.6): sequential repetition makes the extraction guarantee meaningful against provers that pass only with inverse-polynomial probability.
--
--   **Formalization Note** Construction 9.2 is the published protocol of Construction 9.5 with the schedule `sched92`; `Prover95`, `accProb95` and `ExtractsAt95` are used with the constant trajectory $L$. $\log$ is the natural logarithm and $\eta\ge1/p$ is written $1\le p(\lambda)\eta(\lambda)$.
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
--   - reading: a localization parameter Δ(λ) ≤ 1 and a repetition factor γ(λ) → 0 < Δ(λ) ≤ 1; γ : ℕ → ℕ with γ(λ) ≥ 1 and γ polynomially bounded; reason: a localization parameter is positive; the verifier is PPT and sends γ + 1 rounds, each needing a fresh oracle answer, so γ is polynomial; 1/Δ need not be polynomial because the number of rounds does not depend on Δ
--   - reading: 𝒱_R broadcasts "for i = 0, 1"; the verifier checks "for each i ∈ {0, 1}" (Construction 9.2, p.63) → every checkpoint i = 0, …, γ is broadcast by both verifiers and checked; reason: a slip left over from Construction 8.3: 𝒱_L's line and the proof ("∏_{i=0}^γ q_i = η") use every checkpoint (base D3)
--   - reading: Construction 9.2's oracles, anchor state and acceptance test → the published protocol of Construction 9.5 (Prover95, initState95, Accepts95, accProb95) with the schedule sched92 (checkpoints t + iδ, δ = Δ/(γ + 2), i = 0, …, γ); reason: Construction 9.2 is Construction 9.5's setup, oracles and acceptance test with this schedule; θ_i = 𝒪_Chal(x_{L,i} ⊕ x_{R,i})
--   - reading: Pr[F(σ, ρ_{𝐀𝐁*}) ≥ β(λ, η)] ≥ β′(λ, η) with an unbounded local extractor ℰ(pp, 𝐁*) → ExtractsAt: an extractor given pp and the heard transcripts, a finite Kraus family with ∑ K†K ≤ 1 from the region's cells to n qubits (its success branch); with ρ̂ the success-branch output averaged over all randomness, Tr ρ̂ ≥ η and ⟨ψ|ρ̂|ψ⟩ ≥ β · Tr ρ̂; reason: the success event averaged over all randomness, as in the published goal (base D9); merging the outcomes of fidelity ≥ β into one branch loses nothing
--   - encoding: F(σ, ρ_{𝐀𝐁*}) for σ = |EPR⟩⟨EPR|^{⊗n} → ⟨EPR^{⊗n}|ρ|EPR^{⊗n}⟩ (fidPure), the j-th anchor qubit paired with the j-th output qubit; reason: the squared-fidelity convention of Definition 8.1 and Theorem 7.9; for a pure σ it is the stronger of the two conventions (base D10)
--   - encoding: log(1/η) and η(λ) ≥ 1/p(λ) → Real.log (natural logarithm); 1 ≤ p(λ) · η(λ) for a polynomially bounded p : ℕ → ℕ; reason: another base of the logarithm changes only C
--   - encoding: γ = cλt⁴ for a polynomial t(λ) → γ(λ) = max(1, ⌈c · λ · q(λ)⁴⌉) for every polynomially bounded q with q ≥ 1, the conclusion for all λ ≥ λ₀; reason: the printed γ is not an integer and is 0 at λ = 0, where it is not a repetition factor; the negl term of the main clause can exceed 1/q(λ) at small λ, so β ≥ 1 − 1/t(λ) holds eventually (base D16)
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.3, p.63, with Definition 9.1, pp.61–62, and Construction 9.2, pp.62–63

import Definitions.Def_QubitTracking_Supplement_sched92
import Definitions.Def_QubitTracking_Supplement_ndDist95

set_option autoImplicit false

namespace QubitTracking.Supplement

/-- **Theorem 9.3** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time
(Or: Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.3,
p.63, with Definition 9.1, pp.61–62, and Construction 9.2, pp.62–63; pinned down in the model of
the base mission). Construction 9.2 is a non-destructive entanglement localization scheme for
`σ = |EPR⟩⟨EPR|^{⊗n}` in the classical oracle model with 1-Completeness and `(β, β′, Δ)`-Extraction
Soundness, `β(λ, η) = 1 − O((log(1/η)/γ)^{1/4}) − negl(λ)`, `β′(λ, η) = η(λ)`; in particular, for
any polynomial `q(λ)`, setting `γ = cλq⁴` for some constant `c` achieves `β(λ, η) ≥ 1 − 1/q(λ)`.

The clauses:
1. *1-Completeness and non-destructiveness*: for every claimed point `(L, t)` there is a QPT prover
   family at position `L`, accepted with probability `1` at every `λ`, with negligible expected
   trace distance between the setup state on `𝐀𝐁` and the state on `𝐀𝐁′` after `Localize`.
2. *Extraction soundness*: a universal constant `C > 0` such that for all parameters, every claimed
   point `(L, t)`, every QPT prover family `P*` with `η(λ) = accProb ≥ 1/p(λ)` for a polynomial `p`,
   there is a negligible `ν` such that at every `λ` a local extractor on
   `register[[L − Δ, L + Δ] @ t]` succeeds with probability `≥ η(λ)` and conditional fidelity
   `≥ 1 − C (log(1/η(λ))/γ(λ))^{1/4} − ν(λ)`.
3. *In particular*: for every polynomial `q ≥ 1` there is `c > 0` such that with
   `γ(λ) = max(1, ⌈cλq(λ)⁴⌉)`, every such prover admits, for all large `λ`, a local extractor with
   success probability `≥ η(λ)` and conditional fidelity `≥ 1 − 1/q(λ)`.

**Formalization Note** Construction 9.2 is Construction 9.5's protocol with the schedule
`sched92` (checkpoints `t + iδ`, `i = 0..γ`); `Prover95`, `accProb95` and `ExtractsAt95` are reused
with the constant trajectory `fun _ => L`. `log` is the natural logarithm; `η ≥ 1/p` is written
`1 ≤ p(λ)·η(λ)`. -/
theorem theorem_9_3 :
    (∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params92 n m Δ γ →
      ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
        ∃ P : (l : ℕ) → Prover95 (n l) (m l) l (sched92 L t (Δ l) (γ l)),
          IsQPT P ∧ (∀ l, IsAtPoint (P l) L) ∧ (∀ l, accProb95 (P l) = 1) ∧
            ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧ ∀ l, ndDist95 (P l) ≤ ν l) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params92 n m Δ γ →
        ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
          ∀ P : (l : ℕ) → Prover95 (n l) (m l) l (sched92 L t (Δ l) (γ l)), IsQPT P →
            ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
              (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb95 (P l)) →
                ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
                  ∀ l, ExtractsAt95 (P l) (fun _ => L) (Δ l) t (accProb95 (P l))
                    (1 - C * (Real.log (1 / accProb95 (P l)) / (γ l : ℝ)) ^ (1 / 4 : ℝ)
                      - ν l)) ∧
    (∀ q : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded q → (∀ l, 1 ≤ q l) →
      ∃ c : ℝ, 0 < c ∧
        ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ),
          Params92 n m Δ (fun l => max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊) →
          ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
            ∀ P : (l : ℕ) → Prover95 (n l) (m l) l
                (sched92 L t (Δ l) (max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊)), IsQPT P →
              ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
                (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb95 (P l)) →
                  ∃ l₀ : ℕ, ∀ l ≥ l₀,
                    ExtractsAt95 (P l) (fun _ => L) (Δ l) t (accProb95 (P l))
                      (1 - 1 / (q l : ℝ))) := by sorry

end QubitTracking.Supplement

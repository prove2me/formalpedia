-- Prove2me | Theorems.Thm_QubitTracking_Supplement_theorem_9_9
-- name    : QubitTracking.Supplement.theorem_9_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:17:40.710026+00:00
-- url     : https://prove2.me/theorems/ae4d089e-ace7-46f9-830a-0df8c77eccc3
-- title:
--   Theorem 9.9 — state localization for any union of orthonormal bases: non-destructive, 1-complete, extraction soundness, and $\zeta$-uniqueness with $\zeta$ the optimal cloning fidelity
-- statement:
--   **Theorem 9.9.** Let $\mathcal S=\{|\psi_i\rangle\}$ be a set of $n$-qubit states that is a union of orthonormal bases, $\mathcal S=\bigcup_j\mathcal B_j$ with each $\mathcal B_j$ consisting of $2^n$ orthonormal states. Then Construction 9.8 is a non-destructive state localization scheme for $\mathcal S$ in the classical oracle model with $\alpha(\lambda)=1$, $(\beta,\beta',\Delta)$-Extraction Soundness for
--   $$\beta(\lambda,\eta)=1-O\Big(\Big(\frac{\log(1/\eta)}{\gamma}\Big)^{1/4}\Big)-\mathsf{negl}(\lambda),\qquad\beta'(\lambda,\eta)=\eta(\lambda),$$
--   and uniqueness parameter
--   $$\zeta(\lambda):=\sup_{\mathcal A}\ \mathbb E\big[\langle\psi_i|\langle\psi_i|\,\rho\,|\psi_i\rangle|\psi_i\rangle:\ |\psi_i\rangle\leftarrow\mathcal S,\ \rho\leftarrow\mathcal A(|\psi_i\rangle)\big].$$
--   In particular, for any polynomial $q(\lambda)$, setting $\gamma=c\lambda q^4$ for some constant $c$ achieves $\beta(\lambda,\eta)\ge1-1/q(\lambda)$.
--
--   The family is given at each $\lambda$ by $k(\lambda)\ge1$ unitaries $U_{\lambda,j}$ on $n(\lambda)$ qubits, $\mathcal S_\lambda=\{U_{\lambda,j}|x\rangle\}$, indexed by $(j,x)$. Precisely, the theorem asserts:
--
--   1. **Completeness and non-destructiveness.** For all parameters ($n(\lambda),m(\lambda)\ge\lambda$ polynomially bounded, $0<\Delta(\lambda)\le1$, a polynomially bounded $\gamma(\lambda)\ge1$), every family and every claimed point $(L,t)$, there is a QPT prover family at position $L$, accepted with probability $1$ at every $\lambda$, whose expected trace distance between $\mathrm{Enc}|\psi_i\rangle\langle\psi_i|\mathrm{Enc}^\dagger$ and the state on $\mathbf B'$ after $\mathsf{Localize}$ is negligible.
--   2. **Extraction soundness.** There is a universal constant $C>0$, independent of the family, such that for all parameters, every family, every claimed point $(L,t)$ and every QPT prover family $\mathcal P^*$ with $\eta(\lambda)\ge1/p(\lambda)$ for a polynomial $p$, there is a negligible $\nu$ such that at every $\lambda$ a local extractor on $\mathsf{register}[[L-\Delta,L+\Delta]@t]$, which knows neither $i$ nor the secret parameters, outputs $|\psi_i\rangle$ with success probability at least $\eta(\lambda)$ and conditional fidelity at least
--   $$1-C\Big(\frac{\log(1/\eta(\lambda))}{\gamma(\lambda)}\Big)^{1/4}-\nu(\lambda).$$
--   3. **$\zeta$-Uniqueness.** At every $\lambda$, for every (unbounded) prover, every claimed point, every two disjoint spatial regions $S_0,S_1$, every time $t'$ and every two local channels acting on $\mathsf{register}[S_0@t']$ and $\mathsf{register}[S_1@t']$, the expected fidelity of their joint output with $|\psi_i\rangle|\psi_i\rangle$ is at most $\zeta(\lambda)$.
--   4. **In particular.** For every polynomial $q\ge1$ there is $c>0$ such that with $\gamma(\lambda)=\max(1,\lceil c\lambda q(\lambda)^4\rceil)$, every such prover admits, for all sufficiently large $\lambda$, a local extractor with success probability at least $\eta(\lambda)$ and conditional fidelity at least $1-1/q(\lambda)$.
--
--   Covered families include BB84 states and coset states; uniqueness means that no two separated parties can both hold the localized state better than the family's optimal cloner.
--
--   **Formalization Note** The protocol is `Prover98`, `initState98`, `Accepts98`, `accProb98` on the schedule `sched92`; extraction is `ExtractsAt98`, uniqueness `uniqVal98` and `zeta98`. $\log$ is the natural logarithm and $\eta\ge1/p$ is written $1\le p(\lambda)\eta(\lambda)$.
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
--   - reading: a localization parameter Δ(λ) ≤ 1 and a repetition factor γ(λ) → 0 < Δ(λ) ≤ 1; γ : ℕ → ℕ with γ(λ) ≥ 1 and γ polynomially bounded; reason: a localization parameter is positive; the verifier is PPT and sends γ + 1 rounds, each needing a fresh oracle answer, so γ is polynomial; 1/Δ need not be polynomial because the number of rounds does not depend on Δ
--   - reading: 𝒱_R broadcasts "for i = 0, 1"; the verifier checks "for each i ∈ {0, 1}" (Construction 9.2, p.63) → every checkpoint i = 0, …, γ is broadcast by both verifiers and checked; reason: a slip left over from Construction 8.3: 𝒱_L's line and the proof ("∏_{i=0}^γ q_i = η") use every checkpoint (base D3)
--   - reading: Construction 9.8's S, T, u, v ("the same marginal distribution as in GenAnchorState"; v ← CS(T), u ← CS(S^⊥)) → the anchor data of Definition 4.2 with n_e = n_h = n_s = n (anchorS, anchorT, anchorU, anchorV) from uniform U_shift, u′, v′; reason: the construction says the data have GenAnchorState's distribution
--   - reading: 𝒮 = ⋃_j ℬ_j, a union of orthonormal bases of n qubits; |ψ_i⟩ ← 𝒮 → for each λ, k(λ) ≥ 1 unitaries U_{λ,j} on n(λ) qubits; ψ_{(j,x)} = U_{λ,j}|x⟩ with (j, x) uniform in Fin k × 𝔽₂ⁿ; no bound on k; reason: the paper rewrites 𝒮 as ⋃_{U∈𝒰}{U|x⟩} (p.70) and footnote 17 indexes it by (U, x); footnote 15 lets 𝒮 depend on λ
--   - encoding: 𝒱_L broadcasts (θ_i, x_{L,i}), 𝒱_R broadcasts x_{R,i} → both messages have λ + 1 bits: 𝒱_R's is padded with a leading 0 bit; reason: the padding bit is fixed and carries no information
--   - reading: Pr[⟨ψ_i|ρ_{𝐁*}|ψ_i⟩ ≥ β(λ, η)] ≥ β′(λ, η) for an unbounded local extractor ℰ(pp, 𝐁*) that does not know i → ExtractsAt98: an extractor given pp = 𝒪 and the heard transcripts (not i, not sp), a finite Kraus family with ∑ K†K ≤ 1 from the region's cells to n qubits; with ρ̂_ω its success-branch output, 𝔼_ω Tr ρ̂_ω ≥ η and 𝔼_ω ⟨ψ_{i(ω)}|ρ̂_ω|ψ_{i(ω)}⟩ ≥ β · 𝔼_ω Tr ρ̂_ω; reason: the success event averaged over all randomness, as in the published goal (base D9); footnote 16
--   - reading: ζ(λ) := sup_𝒜 𝔼[⟨ψ_i|⟨ψ_i| ρ |ψ_i⟩|ψ_i⟩ : |ψ_i⟩ ← 𝒮, ρ ← 𝒜(|ψ_i⟩)] → zeta98: the real supremum over all channels (finite Kraus families with ∑ K†K = 1, WildeQIT.QChannel) from n to 2n qubits of the uniform average over the index; reason: every channel between finite-dimensional systems has a finite Kraus decomposition; the set is nonempty and bounded by 1
--   - generalization: ζ-Uniqueness: for any (potentially unbounded) prover, disjoint spatial regions L₀, L₁, times t, t′ and local adversaries 𝒜, ℬ on 𝐀* = register[L₀ @ t′], 𝐁* = register[L₁ @ t′] → every valid prover (no gate bound), every claimed (L, t), every two disjoint sets S₀, S₁ ⊆ ℝ, every t′, and every two channels to n qubits on register[S₀ @ t′] and register[S₁ @ t′] that may also read pp and the transcripts heard in their region; the bound holds at every λ; reason: disjoint sets include disjoint intervals, and giving the adversaries pp and their heard transcripts only enlarges the class; the composite of setup, prover and adversaries is still a channel from |ψ_i⟩ independent of i
--   - encoding: the state family's states on register 𝐁, no anchor → the anchor register is Fin 0 (empty); reason: the published register model carries an anchor slot; here it is empty
--   - encoding: log(1/η) and η(λ) ≥ 1/p(λ) → Real.log (natural logarithm); 1 ≤ p(λ) · η(λ) for a polynomially bounded p : ℕ → ℕ; reason: another base of the logarithm changes only C
--   - encoding: γ = cλt⁴ for a polynomial t(λ) → γ(λ) = max(1, ⌈c · λ · q(λ)⁴⌉) for every polynomially bounded q with q ≥ 1, the conclusion for all λ ≥ λ₀; reason: the printed γ is not an integer and is 0 at λ = 0, where it is not a repetition factor; the negl term of the main clause can exceed 1/q(λ) at small λ, so β ≥ 1 − 1/t(λ) holds eventually (base D16)
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.9, p.70, with Definition 9.7, pp.68–69, Construction 9.8, pp.69–70, and footnotes 15–17

import Definitions.Def_QubitTracking_Supplement_sched92
import Definitions.Def_QubitTracking_Supplement_zeta98

set_option autoImplicit false

namespace QubitTracking.Supplement

/-- **Theorem 9.9** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time
(Or: Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.9,
p.70, with Definition 9.7, pp.68–69, and Construction 9.8, pp.69–70; pinned down in the model of
the base mission). Let `𝒮` be a union of orthonormal bases of `n` qubits. Construction 9.8 is a
non-destructive state localization scheme for `𝒮` in the classical oracle model with `α(λ) = 1`,
`(β, β′, Δ)`-Extraction Soundness for `β(λ, η) = 1 − O((log(1/η)/γ)^{1/4}) − negl(λ)`,
`β′(λ, η) = η(λ)`, and uniqueness parameter
`ζ(λ) = sup_𝒜 𝔼[⟨ψ_i|⟨ψ_i| 𝒜(|ψ_i⟩) |ψ_i⟩|ψ_i⟩ : |ψ_i⟩ ← 𝒮]`; in particular, for any polynomial
`q(λ)`, setting `γ = cλq⁴` for some constant `c` achieves `β(λ, η) ≥ 1 − 1/q(λ)`.

The family is given at each `λ` by `k(λ) ≥ 1` unitaries `U_{λ,j}` on `n(λ)` qubits,
`𝒮_λ = {U_{λ,j}|x⟩}`, indexed by `(j, x)` (footnote 17). The clauses:
1. *1-Completeness and non-destructiveness*: for every claimed point `(L, t)` there is a QPT prover
   family at position `L`, accepted with probability `1` at every `λ`, with negligible expected
   trace distance between `Enc|ψ_i⟩⟨ψ_i|Enc†` and the state on `𝐁′` after `Localize`.
2. *Extraction soundness*: a universal constant `C > 0` (independent of the family) such that for
   all parameters, every family, every claimed point `(L, t)`, every QPT prover family `P*` with
   `η(λ) ≥ 1/p(λ)` for a polynomial `p`, there is a negligible `ν` such that at every `λ` a local
   extractor on `register[[L − Δ, L + Δ] @ t]`, which sees neither `i` nor `sp`, outputs `|ψ_i⟩`
   with success probability `≥ η(λ)` and conditional fidelity
   `≥ 1 − C (log(1/η(λ))/γ(λ))^{1/4} − ν(λ)`.
3. *`ζ`-Uniqueness*: at every `λ`, for every (unbounded) prover, every claimed point, every two
   disjoint spatial regions `S₀, S₁`, every time `t′` and every two local channels on
   `register[S₀ @ t′]` and `register[S₁ @ t′]`, the expected fidelity of their joint output with
   `|ψ_i⟩|ψ_i⟩` is at most `ζ(λ)`.
4. *In particular*: for every polynomial `q ≥ 1` there is `c > 0` such that with
   `γ(λ) = max(1, ⌈cλq(λ)⁴⌉)`, every such prover admits, for all large `λ`, a local extractor with
   success probability `≥ η(λ)` and conditional fidelity `≥ 1 − 1/q(λ)`.

**Formalization Note** The protocol is `Prover98`, `initState98`, `Accepts98`, `accProb98` with
the schedule `sched92`; extraction is `ExtractsAt98`, uniqueness `uniqVal98` and `zeta98`. `log`
is the natural logarithm; `η ≥ 1/p` is written `1 ≤ p(λ)·η(λ)`. -/
theorem theorem_9_9 :
    (∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params92 n m Δ γ →
      ∀ (k : ℕ → ℕ) (F : (l : ℕ) → StateFam (n l) (k l)), (∀ l, 1 ≤ k l) →
        ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
          ∃ P : (l : ℕ) → Prover98 (n l) (m l) l (sched92 L t (Δ l) (γ l)),
            IsQPT P ∧ (∀ l, IsAtPoint (P l) L) ∧ (∀ l, accProb98 (P l) (F l) = 1) ∧
              ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧ ∀ l, ndDist98 (P l) (F l) ≤ ν l) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params92 n m Δ γ →
        ∀ (k : ℕ → ℕ) (F : (l : ℕ) → StateFam (n l) (k l)), (∀ l, 1 ≤ k l) →
          ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
            ∀ P : (l : ℕ) → Prover98 (n l) (m l) l (sched92 L t (Δ l) (γ l)), IsQPT P →
              ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
                (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb98 (P l) (F l)) →
                  ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
                    ∀ l, ExtractsAt98 (P l) (F l) L (Δ l) t (accProb98 (P l) (F l))
                      (1 - C * (Real.log (1 / accProb98 (P l) (F l)) / (γ l : ℝ)) ^ (1 / 4 : ℝ)
                        - ν l)) ∧
    (∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params92 n m Δ γ →
      ∀ (k : ℕ → ℕ) (F : (l : ℕ) → StateFam (n l) (k l)), (∀ l, 1 ≤ k l) →
        ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ, ∀ l : ℕ,
          ∀ P : Prover98 (n l) (m l) l (sched92 L t (Δ l) (γ l)), P.Valid →
            ∀ (S₀ S₁ : Set ℝ), Disjoint S₀ S₁ → ∀ t' : ℝ,
              ∀ (A : LocalAdv98 (n l) (m l) l P (regionOn P t' S₀))
                (B : LocalAdv98 (n l) (m l) l P (regionOn P t' S₁)),
                uniqVal98 P (F l) S₀ S₁ t' A B ≤ zeta98 (F l)) ∧
    (∀ q : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded q → (∀ l, 1 ≤ q l) →
      ∃ c : ℝ, 0 < c ∧
        ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ),
          Params92 n m Δ (fun l => max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊) →
          ∀ (k : ℕ → ℕ) (F : (l : ℕ) → StateFam (n l) (k l)), (∀ l, 1 ≤ k l) →
            ∀ L ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ,
              ∀ P : (l : ℕ) → Prover98 (n l) (m l) l
                  (sched92 L t (Δ l) (max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊)), IsQPT P →
                ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
                  (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb98 (P l) (F l)) →
                    ∃ l₀ : ℕ, ∀ l ≥ l₀,
                      ExtractsAt98 (P l) (F l) L (Δ l) t (accProb98 (P l) (F l))
                        (1 - 1 / (q l : ℝ))) := by sorry

end QubitTracking.Supplement

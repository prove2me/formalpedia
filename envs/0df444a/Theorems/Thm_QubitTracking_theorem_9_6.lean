-- Prove2me | Theorems.Thm_QubitTracking_theorem_9_6
-- name    : QubitTracking.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:49.826919+00:00
-- url     : https://prove2.me/theorems/a8be0e98-86af-4e12-8f34-ddea1eb57430
-- title:
--   Theorem 9.6 — trajectory verification: perfect completeness; $n$ EPR pairs extractable near every point of $L$ with probability $\eta$ and fidelity $1-O((\log(1/\eta)/\gamma)^{1/4})-\mathrm{negl}$
-- statement:
--   Construction 9.5 is a trajectory verification scheme for $\sigma=|\mathrm{EPR}\rangle\langle\mathrm{EPR}|^{\otimes n}$ in the classical oracle model with $1$-Completeness and $(\beta,\beta',\Delta)$-Extraction Soundness, where
--   $$\beta(\lambda,\eta)=1-O\Big(\Big(\frac{\log(1/\eta)}{\gamma}\Big)^{1/4}\Big)-\mathrm{negl}(\lambda),\qquad\beta'(\lambda,\eta)=\eta(\lambda).$$
--   In particular, for any polynomial $q(\lambda)$, setting $\gamma=c\lambda q^4$ for some constant $c$ gives $\beta(\lambda,\eta)\ge1-1/q(\lambda)$.
--
--   In the pinned-down model this is three statements:
--
--   1. **Completeness.** For every valid trajectory $L$ on $[0,\tau]$ there is a QPT prover family moving along $L$ that the verifier accepts with probability $1$ at every $\lambda$.
--   2. **Extraction soundness.** There is a universal $C>0$ such that for all admissible parameters, every valid trajectory and every QPT prover family $P^*$ whose acceptance probability satisfies $\eta(\lambda)\ge1/p(\lambda)$ for a polynomial $p$, there is a negligible $\nu$ such that at every $\lambda$ and every time $t\in[0,\tau]$ some local extractor, acting on $\mathsf{pp}$, the transcript heard in $[L(t)-\Delta,L(t)+\Delta]@t$ and the prover's registers there, succeeds with probability at least $\eta(\lambda)$ and conditional fidelity with $n$ EPR pairs (with the anchor) at least
--   $$1-C\Big(\frac{\log(1/\eta(\lambda))}{\gamma(\lambda)}\Big)^{1/4}-\nu(\lambda).$$
--   3. **In particular.** For every polynomial $q\ge1$ there is $c>0$ such that with $\gamma(\lambda)=\max(1,\lceil c\lambda q(\lambda)^4\rceil)$, every such prover admits, for all large $\lambda$ and every $t\in[0,\tau]$, a local extractor with success probability at least $\eta(\lambda)$ and conditional fidelity at least $1-1/q(\lambda)$.
--
--   This is the paper's headline result: the first feasibility result for verifying the trajectory of a quantum entity through spacetime.
--
--   **Formalization Note** This is the operator-requested pinned-down version: the spacetime model of §3.2 and the register notation of Definition 3.2 are made precise (definitions `Prover`, `regionMem`, `regState`, `sched95`, `ExtractsAt95`), and each modelling choice is listed below.
--
--   Differences from the source:
--   - reading: time ℝ≥0 (§3.2, p.21) → time ℝ; reason: Construction 9.5 broadcasts at iδ − (L̃(iδ) + 1), which is negative for small i (p.66)
--   - reading: 'for i = 0, 1' in 𝒱_R's broadcast line and 'for each i ∈ {0, 1}' in the acceptance test (p.66) → every round i = 0, …, N is sent and checked; reason: a leftover from Construction 8.3; 𝒱_L's line sends every round and the proof uses every checkpoint (∏_{i=0}^N q_i = η, p.66)
--   - reading: the prose spacetime model of §3.2 (cells, trajectories, circuits at intersection points, message cells) → one-qubit cells with 1-Lipschitz trajectories in [−1, 1], a time-sorted list of located gates acting only on co-located cells, challenge cells on light rays, response cells at the verifier at the deadline (Prover, Prover.Valid); reason: the most standard precise reading of pp.21–23; a multi-qubit cell is a bundle of one-qubit cells
--   - generalization: QPT prover P*: polynomially many gates of some fixed universal gate set (p.22) → every one- or two-qubit unitary and every oracle query counts as one gate; reason: every such gate set consists of one- and two-qubit gates, so soundness covers every QPT prover of the paper
--   - reading: the QPT prover of 1-Completeness → a prover family in the same gate model (any one- or two-qubit unitary counts as one gate); reason: the paper does not fix the gate set; the honest prover uses only Hadamard, CNOT, controlled-Hadamard and oracle queries, which a standard gate set implements exactly
--   - encoding: 𝒪 with values in 𝔽₂^m ∪ {⊥} → answers encoded in m + 1 qubits, y ↦ (y, 0), ⊥ ↦ (0^m, 1); reason: a faithful encoding of the output set
--   - encoding: classical challenges broadcast at their times; responses received at their deadlines; a missing response gives ⊥ → challenges written into their message cells at the start, responses measured at the end, a missing response is any value failing the test; reason: no gate may touch a message cell outside its window, so the probabilities agree
--   - reading: register[(L(t))_Δ @ t] (Definition 3.2) → the reduced state of the anchor and the cells in [L(t) − Δ, L(t) + Δ] at time t, without challenges not yet broadcast and responses already due, plus the heard transcript given to the extractor as classical input; reason: items 1–3 of Definition 3.2; the anchor enters only through the fidelity
--   - reading: Pr[F(σ, ρ_{𝐀𝐁*}) ≥ β(λ, η)] ≥ β′(λ, η) → the extractor's success branch, averaged over all randomness, has trace ≥ η and EPR fidelity ≥ β · trace (ExtractsAt95); reason: Definition 8.1 (p.56) and Theorem 7.9 (p.55) measure expected fidelity, and the proof concludes 'with probability at least η outputs a state having the following fidelity' (pp.67–68)
--   - encoding: fidelity F(σ, ρ) with σ = |EPR⟩⟨EPR|^{⊗n} → ⟨EPR^{⊗n}|ρ|EPR^{⊗n}⟩, the j-th anchor qubit paired with the j-th output qubit; reason: the convention of Definition 8.1 and Theorem 7.9
--   - reading: β = 1 − O((log(1/η)/γ)^{1/4}) − negl(λ) → a universal constant C > 0 before all parameters, and a negligible ν chosen after the prover and p; log is the natural logarithm; reason: the O-constant comes from Lemma 7.6 and Theorem 7.9 and is universal; another log base changes only C
--   - reading: parameters n(λ), m(λ) ≥ λ polynomials, Δ(λ) ≤ 1, a repetition factor γ(λ), a PPT verifier (pp.64–65) → n, m polynomially bounded with n, m ≥ λ; 0 < Δ ≤ 1; γ ≥ 1; 1/Δ and γ polynomially bounded; L and τ fixed; reason: the verifier sends ⌈τ(γ+2)/Δ⌉ + γ + 1 rounds and must be PPT; the definition fixes L before the function η(λ)
--   - reading: 'any trajectory L' in Extraction Soundness (p.65) → valid trajectories: L([0, τ]) ⊆ [−1, 1] and 1-Lipschitz on [0, τ]; reason: §3.2 assumes every prover trajectory is continuous with values in [−1, 1] and speed at most one (p.23, standing assumption); Definition 9.4's syntax takes 'a continuous trajectory' (p.64) and the proof uses that the valid trajectory has speed at most one (p.68)
--   - reading: a QPT prover 'moving along L' (p.65) → every gate located at (L̃(s), s) and the input cells following L̃, with L̃(s) = L(min(max(s, 0), τ)); reason: the honest prover holds 𝐁 while moving along L and remains at L(τ) afterwards (p.66)
--   - encoding: |Ψ^{sk}⟩ generated by EPR pairs and measurements (Definition 4.2) → its closed form (p.27) with uniform U_shift, u′, v′; reason: the closed form is the normalized post-measurement state
--   - reading: 'we can set γ = cλt⁴ for some constant c to achieve β(λ, η) ≥ 1 − 1/t(λ)' → ∀ polynomial q ≥ 1 ∃ c > 0 such that, with γ = max(1, ⌈cλq⁴⌉), for every admissible prover there is λ₀ with fidelity ≥ 1 − 1/q(λ) for all λ ≥ λ₀; reason: the negligible term of the main clause can exceed 1/q(λ) at small λ; the max only changes λ = 0, where cλq⁴ = 0 is not a repetition factor
--   - encoding: 1-Completeness: Pr[b = ⊤] ≥ 1 → accProb = 1; reason: an acceptance probability is at most 1
--   - encoding: η(λ) ≥ 1/p(λ) for a polynomial p → 1 ≤ p(λ)·η(λ) for a polynomially bounded p; reason: the same condition, written without division by p(λ) = 0
--   - encoding: 𝒪_Chal, 𝒪_random random oracles; pp = (𝒪_Chal, 𝒪) given to the extractor → uniformly random functions; the extractor reads pp as functions; reason: Remark 8.2 allows an unbounded extractor, which can read the oracles off by queries
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.6, p.66 (Definition 9.4, pp.64–65; Construction 9.5, pp.65–66)

import Definitions.Def_QubitTracking_sched95

set_option autoImplicit false

namespace QubitTracking

/-- **Theorem 9.6** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time
(Or: Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.6,
p.66; operator-requested pinned-down version). Construction 9.5 is a trajectory verification
scheme for `σ = |EPR⟩⟨EPR|^{⊗n}` in the classical oracle model with 1-Completeness and
`(β, β′, Δ)`-Extraction Soundness, `β(λ, η) = 1 − O((log(1/η)/γ)^{1/4}) − negl(λ)`,
`β′(λ, η) = η(λ)`; in particular, for any polynomial `q(λ)`, setting `γ = cλq⁴` for some constant
`c` achieves `β(λ, η) ≥ 1 − 1/q(λ)`.

The three clauses:
1. *1-Completeness*: for every valid trajectory there is a QPT prover family moving along it that
   is accepted with probability `1` at every `λ`.
2. *Extraction soundness*: a universal constant `C > 0` such that for all parameters, every valid
   trajectory, every QPT prover family `P*` with `η(λ) = accProb ≥ 1/p(λ)` for a polynomial `p`,
   there is a negligible `ν` such that at every `λ` and every time `t ∈ [0, τ]` a local extractor
   succeeds with probability `≥ η(λ)` and conditional fidelity
   `≥ 1 − C (log(1/η(λ))/γ(λ))^{1/4} − ν(λ)`.
3. *In particular*: for every polynomial `q ≥ 1` there is `c > 0` such that with
   `γ(λ) = max(1, ⌈cλq(λ)⁴⌉)`, every such prover admits, for all large `λ` and every `t ∈ [0, τ]`,
   a local extractor with success probability `≥ η(λ)` and conditional fidelity `≥ 1 − 1/q(λ)`.

**Formalization Note** The spacetime model of §3.2 and the register notation of Definition 3.2
are pinned down in `Prover`, `Prover.Valid`, `IsQPT`, `regionMem`, `regState`; the protocol in
`sched95`, `oracleO`, `initState95`, `Accepts95`, `accProb95`; the extraction event in
`ExtractsAt95` (success branch averaged over all randomness, fidelity `⟨ψ|ρ|ψ⟩`). `log` is the
natural logarithm (another base changes only `C`). `η ≥ 1/p` is written `1 ≤ p(λ)·η(λ)`. -/
theorem theorem_9_6 :
    (∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params95 n m Δ γ →
      ∀ (L : ℝ → ℝ) (τ : ℝ), ValidTrajectory L τ →
        ∃ P : (l : ℕ) → Prover95 (n l) (m l) l (sched95 L τ (Δ l) (γ l)),
          IsQPT P ∧ IsMovingAlong P L τ ∧ ∀ l, accProb95 (P l) = 1) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ), Params95 n m Δ γ →
        ∀ (L : ℝ → ℝ) (τ : ℝ), ValidTrajectory L τ →
          ∀ P : (l : ℕ) → Prover95 (n l) (m l) l (sched95 L τ (Δ l) (γ l)), IsQPT P →
            ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
              (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb95 (P l)) →
                ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
                  ∀ l, ∀ t ∈ Set.Icc 0 τ,
                    ExtractsAt95 (P l) L (Δ l) t (accProb95 (P l))
                      (1 - C * (Real.log (1 / accProb95 (P l)) / (γ l : ℝ)) ^ (1 / 4 : ℝ)
                        - ν l)) ∧
    (∀ q : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded q → (∀ l, 1 ≤ q l) →
      ∃ c : ℝ, 0 < c ∧
        ∀ (n m : ℕ → ℕ) (Δ : ℕ → ℝ),
          Params95 n m Δ (fun l => max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊) →
          ∀ (L : ℝ → ℝ) (τ : ℝ), ValidTrajectory L τ →
            ∀ P : (l : ℕ) → Prover95 (n l) (m l) l
                (sched95 L τ (Δ l) (max 1 ⌈c * (l : ℝ) * (q l : ℝ) ^ 4⌉₊)), IsQPT P →
              ∀ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p →
                (∀ l, (1 : ℝ) ≤ (p l : ℝ) * accProb95 (P l)) →
                  ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ t ∈ Set.Icc 0 τ,
                    ExtractsAt95 (P l) L (Δ l) t (accProb95 (P l)) (1 - 1 / (q l : ℝ))) := by sorry

end QubitTracking

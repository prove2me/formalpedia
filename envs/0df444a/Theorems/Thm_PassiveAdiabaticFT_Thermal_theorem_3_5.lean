-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_theorem_3_5
-- name    : PassiveAdiabaticFT.Thermal.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:23.285026+00:00
-- url     : https://prove2.me/theorems/4ce3383e-be9a-44af-b90b-5b6163c79577
-- title:
--   Theorem 3.5 — log-local constant-strength protected adiabatic computation under thermal noise (corrected: 1+γ+κ in the locality logarithm)
-- statement:
--   For every bath inverse temperature $\beta>0$ there is a constant $C>0$ (depending on $\beta$ only) such that for all rate bounds $\gamma,\kappa\ge0$, all $n\ge1$, $T\ge0$, $\varepsilon>0$ and every circuit $\mathcal C$ of $T$ gates on $n$ qubits there is a protected adiabatic path — $N$ blocks of a stabilizer code with a Pauli decoder ($R_0=I$), penalty $0<J\le C$, duration $T'$, logical Hamiltonians $K_0,K_1$ given as sums of Hermitian terms with $|0\cdots0\rangle$ a ground state of $K_0$, output logical qubits, and physical path $H(t)=\sum_iH_0^{(i)}+\hat K(t)$ with $K(t)=(1-t/T')K_0+(t/T')K_1$ — such that, writing $L=\log\big(2+(1+\gamma+\kappa)\,n(T+1)/\varepsilon\big)$:
--
--   1. every interaction term (each penalty $J(I-P_a^{(i)})$ and each dressed term $\hat K_{0,A},\hat K_{1,A}$) has operator norm at most $C$, and so does, for every set $S$ of physical qubits, the sum of the penalty terms (resp. of the $\hat K_{0,A}$, of the $\hat K_{1,A}$) whose support is exactly $S$;
--   2. every interaction term acts on at most $C\,L$ physical qubits;
--   3. the number of physical qubits is at most $C\,(n+(T+1)/\varepsilon)\,L$;
--   4. $T'\le C(2+n+T+1/\varepsilon)^C$;
--   5. for every family of rates and Lamb coefficients satisfying (1.18)–(1.19) at $\beta$ with bounds $\gamma,\kappa$, for every $\beta'\ge\beta$ and also for the code-space encoding, and for every solution $\rho$ of the noisy equation (1.17)/(3.3) on $[0,T']$ started in $\mathrm{Enc}_{\beta'}^{\otimes N}(|0\cdots0\rangle\langle0\cdots0|)$ (resp. the code-space encoding of $|0\cdots0\rangle$),
--   $$\tfrac12\Big\|\operatorname{Tr}_{\text{non-output}}\big(\mathrm{Dec}^{\otimes N}(\rho(T'))\big)-\mathcal C|0^n\rangle\langle0^n|\mathcal C^\dagger\Big\|_1\le\varepsilon.$$
--
--   In words: an adiabatic path with constant interaction strength and logarithmic locality, on $O((n+T/\varepsilon)\log(nT/\varepsilon))$ qubits and running for polynomial time, simulates any circuit to error $\varepsilon$ under constant-temperature thermal noise, from a thermal initial state at or below the bath temperature or from the code space. This is the paper's main result.
--
--   Differences from the source:
--   - correction: k = O(log(n(γ+κ)T/ε)) (3.40) → locality ≤ C·log(2 + (1+γ+κ)·n·(T+1)/ε); reason: the printed bound is false at γ = κ = 0: all rates and Lamb coefficients zero satisfy (1.18)–(1.19), the logarithm is log 0 (and negative whenever 0 < n(γ+κ)T < ε), while every construction has a term acting on at least one qubit; 1+γ+κ is the proof's R (3.46)
--   - generalization: constant bath bounds γ, κ = O(1) (constants may depend on them) → C depends on β only and the bounds hold uniformly in γ, κ ≥ 0 (the qubit count also carries log(2+(1+γ+κ)…)); reason: for fixed γ, κ, log(2+(1+γ+κ)x) ≤ C′ log(2+x), so the source's bounds follow
--   - generalization: an initial state prepared in inverse temperature β′ ≥ β → also the code-space (ground-space) encoding; reason: stated in the abstract and at the end of the proof of Theorem 3.3 (p. 25); the thermal clause is unchanged
--   - reading: an adiabatic path with constant interaction strength and k-local interactions → a construction record: code blocks with encoder and Pauli decoder (R_0 = I), constant penalty J, dressed linear interpolation (1−t/T′)K_0 + (t/T′)K_1 of Hermitian terms from the all-zero ground state of K_0, Enc/Dec computed from the code (3.44), the logical path allowed on all N·k logical qubits; reason: the paper's construction (p. 9, (3.44)); without the shape the existential would be trivial, and the paper's one-qubit-per-block use is an instance
--   - reading: constant interaction strength → every term has norm ≤ C, and for every set S of physical qubits the merged interaction on S (the sum of the penalty terms, resp. of the dressed K̂_{0,A}, of the dressed K̂_{1,A}, whose support is exactly S) has norm ≤ C; reason: strength is a bound on the interaction on each set of qubits; without the merged bound a term repeated λ times would count as λ terms of norm ≤ C, the logical path could be run λ times faster, and a trivial one-qubit code with a short T′ would meet the error bound with no passive protection
--   - reading: β = O(1), any constant inverse temperature → every fixed β > 0, with all constants chosen after β; reason: the proof chooses J after β ((2.25), p. 25)
--   - reading: can simulate a quantum circuit … up to error ε → ½‖Tr_{non-output} Dec^{⊗N}(ρ(T′)) − 𝒞|0ⁿ⟩⟨0ⁿ|𝒞†‖₁ ≤ ε for every admissible rate family chosen after the construction; reason: the sentence after Theorem 1.8 (p. 11); the construction depends only on β, γ, κ, n, T, ε, 𝒞
--   - encoding: O(·) and poly(T, n, 1/ε), time-ordered exponential of L_β → explicit C, T+1 and 2+ inside bounds and logarithms; every solution continuous on [0, T′] with derivative L_β(t)ρ(t) off a countable set; reason: absolute constants; the 2+ and T+1 avoid log 0 at T = 0; the exceptional set admits jumps of L_β(t) at level crossings
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 25, Theorem 3.5 (3.40) (= Theorem 1.8, p. 11, (1.36)); proof pp. 25–26; simulation notion p. 11; construction (3.44)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Construction

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Theorem 3.5 (p. 25; = Theorem 1.8, p. 11), corrected: `1 + γ + κ` in the locality logarithm.
For every bath inverse temperature `β > 0` there is a constant `C` such that for all rate bounds
`γ, κ ≥ 0`, all `n ≥ 1`, `T`, `ε > 0` and every circuit of `T` gates on `n` qubits, there is a
protected adiabatic path (code blocks, Pauli decoder, constant penalty, dressed linear
interpolation from the all-zero ground state of `K_0`) whose terms have strength `≤ C` (also after
merging the terms of each family that have the same support) and act on
`≤ C log(2 + (1+γ+κ)n(T+1)/ε)` qubits, on `≤ C (n + (T+1)/ε) log(2 + (1+γ+κ)n(T+1)/ε)`
physical qubits, with duration `T' ≤ C (2 + n + T + 1/ε)^C`, such that under every thermal
noise model (1.17) at `β` with bounds `γ, κ`, from a thermal encoding at any `β' ≥ β` or from
the code space, the decoded output is within trace distance `ε` of `𝒞|0ⁿ⟩`. -/
theorem theorem_3_5 :
    ∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
      ∀ (γ κ : ℝ), 0 ≤ γ → 0 ≤ κ → ∀ (n : ℕ), 1 ≤ n → ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      ∀ circ : Circuit n T,
        ∃ X : Construction n,
          X.J ≤ C ∧
          (∀ τ, OpNormLe (X.term τ) C) ∧
          (∀ S : Finset (Fin X.N × Fin X.b),
            OpNormLe (termsOn (fun ia => X.term (Sum.inl ia)) S) C ∧
            OpNormLe (termsOn (fun A => X.term (Sum.inr (Sum.inl A))) S) C ∧
            OpNormLe (termsOn (fun A => X.term (Sum.inr (Sum.inr A))) S) C) ∧
          (∀ τ, ∃ S : Finset (Fin X.N × Fin X.b),
            (S.card : ℝ) ≤ C * Real.log (2 + (1 + γ + κ) * n * ((T : ℝ) + 1) / ε) ∧
              ActsOn (X.term τ) S) ∧
          (X.numQubits : ℝ) ≤
            C * (n + ((T : ℝ) + 1) / ε) * Real.log (2 + (1 + γ + κ) * n * ((T : ℝ) + 1) / ε) ∧
          X.T' ≤ C * (2 + n + T + 1 / ε) ^ C ∧
          ∀ γr κr : Fin X.N × (Fin X.b × Fin 3) → ℝ → ℝ, RatesAdmissible β γ κ γr κr →
            (∀ β' : ℝ, β ≤ β' → ∀ ρ : ℝ → Op (Fin X.N × Fin X.b),
              ρ 0 = X.initTh β' → IsSolution (X.gen γr κr) X.T' ρ →
                traceDist (X.output (ρ X.T')) circ.output ≤ ε) ∧
            (∀ ρ : ℝ → Op (Fin X.N × Fin X.b),
              ρ 0 = X.initCode → IsSolution (X.gen γr κr) X.T' ρ →
                traceDist (X.output (ρ X.T')) circ.output ≤ ε) := by sorry

end PassiveAdiabaticFT.Thermal

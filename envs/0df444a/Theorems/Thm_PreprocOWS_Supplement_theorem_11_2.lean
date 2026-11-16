-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_11_2
-- name    : PreprocOWS.Supplement.theorem_11_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:17:24.162196+00:00
-- url     : https://prove2.me/theorems/435fc0d0-a240-42ef-a851-69b6590f6e74
-- title:
--   Theorem 11.2 — zero-query 1PRS with $S$ qubits of advice: advantage $O(\sqrt S/K)$, so constant advantage needs $\Omega(K^2)$ qubits (corrected: $S\to\max\{S,1\}$)
-- statement:
--   In the 1PRS game (Definition 11.1) a random oracle $R:[K]\times[N]\to\{\pm1\}$ with $K\le N$ is sampled uniformly. The adversary holds an $S$-qubit advice state $\rho_R$ (a density matrix depending arbitrarily on $R$), makes no queries, and accepts with a fixed operator $0\preceq\Pi\preceq I$ on the advice and challenge registers. The challenge is $|\psi_{R,k}\rangle$ for uniform $k$ or a Haar-random state.
--
--   There is a universal constant $C>0$ such that for all $S\ge0$, $1\le K\le N$, every such $\Pi$ and every advice map $R\mapsto\rho_R$:
--
--   1. the expected advantage is bounded:
--   $$
--   \mathbb E_R\Big|\,\mathbb E_k\operatorname{Tr}\big(\Pi(\rho_R\otimes|\psi_{R,k}\rangle\langle\psi_{R,k}|)\big)-\mathbb E_{\psi\sim\mathrm{Haar}}\operatorname{Tr}\big(\Pi(\rho_R\otimes|\psi\rangle\langle\psi|)\big)\Big|\,\le\,C\,\frac{\sqrt{\max\{S,1\}}}{K};
--   $$
--   2. consequently, if this expected advantage is at least $\varepsilon>0$, then $\max\{S,1\}\ge(\varepsilon K/C)^2$: constant advantage requires $\Omega(K^2)$ qubits of advice.
--
--   This is the distinguishing analogue of Theorem 5.2 at $T=0$.
--
--   Differences from the source:
--   - correction: O(√S/K) → C·√(max{S,1})/K; reason: as printed the bound is 0 at S = 0, but K = 1, N = 2 and Π = |+⟩⟨+| give Δ = |⟨ψ_{R,1}|Π|ψ_{R,1}⟩ − 1/2| = 1/2 for every R; the proof's moment order t = S/2 needs t ≥ 1
--   - encoding: Haar-random challenge state → the maximally mixed state I/N in Tr(Π(ρ_R ⊗ I/N)); reason: the Haar average of |ψ⟩⟨ψ| is I/N, the page's (1/N)∑_x Π_{x,x} in (41); an exact identity
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - encoding: maximum over advice ρ_R → ∀ maps ρ from oracles to density matrices on [2^S], with the absolute value inside E_R; reason: a bound for every map is a bound on E_R max; the page bounds E_R‖Y_R‖ ≥ E_R Δ_𝒜(R)
--   - encoding: constant advantage requires Ω(K²) qubits (for K = Θ(N), Ω(N²)) → ∀ ε > 0, ε ≤ E_R Δ → (εK/C)² ≤ max{S,1}, with the same C; reason: Ω(K²) with the constant depending on the advantage ε; the K = Θ(N) parenthetical follows by substituting K ≥ cN
--   - generalization: N = 2^n (§3, p.11) → N any positive integer with 1 ≤ K ≤ N; reason: the case N = 2^n is included; the proof does not use it
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 11.2, p.53 (PDF p.56); Definition 11.1, p.52 (PDF p.55); §11.1, display (41), p.53

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_CompNonlocal_IsEffect
import Definitions.Def_PreprocOWS_Supplement_prsAdv
open Matrix
open scoped ComplexOrder

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 11.2 (Quantum advice lower bound for 1PRS)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.53 (PDF p.56), with a minimal
correction at `S = 0`: any (zero-query) adversary with `S` qubits of advice has distinguishing
advantage bounded by `O(√(max{S,1})/K)` in QROM. Consequently, constant advantage requires
`Ω(K²)` qubits. The page prints `O(√S/K)`.

**Formalization Note.** Correction: as printed the bound is `0` at `S = 0`, but `K = 1`, `N = 2`,
`Π = |+⟩⟨+|` give `Δ = |⟨ψ_{R,1}|Π|ψ_{R,1}⟩ − 1/2| = 1/2` for every `R`; the proof sets `t = S/2` and
needs `t ≥ 1`. The `O(·)` is one universal `C > 0` chosen before `S, K, N` and the adversary; the
second conjunct ("consequently") uses the same `C`: an expected advantage `≥ ε > 0` forces
`max{S,1} ≥ (εK/C)²`. Definition 11.1: `R : [K]×[N] → {±1}` uniform with `1 ≤ K ≤ N`, advice
`ρ_R` any density matrix on `S` qubits depending on `R`, `T = 0`, and the fixed online computation
absorbed into `0 ⪯ Π ⪯ I` on `A ⊗ X`. The Haar-random challenge enters through `I/N` (`prsAdv`). -/
theorem theorem_11_2 : ∃ C : ℝ, 0 < C ∧ ∀ (S K N : ℕ), 1 ≤ K → K ≤ N →
    ∀ P : Matrix (Fin (2 ^ S) × Fin N) (Fin (2 ^ S) × Fin N) ℂ, CompNonlocal.IsEffect P →
    ∀ ρ : Oracle K N → Matrix (Fin (2 ^ S)) (Fin (2 ^ S)) ℂ,
      (∀ R, (ρ R).PosSemidef ∧ (ρ R).trace = 1) →
      avg (fun R => prsAdv P (ρ R) R) ≤ C * Real.sqrt (max (S : ℝ) 1) / K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ avg (fun R => prsAdv P (ρ R) R) →
        (ε * K / C) ^ 2 ≤ max (S : ℝ) 1 := by sorry

end PreprocOWS.Supplement

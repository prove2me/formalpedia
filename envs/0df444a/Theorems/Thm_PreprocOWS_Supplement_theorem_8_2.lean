-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_8_2
-- name    : PreprocOWS.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:12:47.672444+00:00
-- url     : https://prove2.me/theorems/c4c2a545-9b71-4d4e-bc63-fd23c17c07b5
-- title:
--   Theorem 8.2 — PRG with $S$ qubits of advice and $T$ queries: advantage $O\big(T^2/N+\sqrt{S(T+1)/N}\big)$ (corrected: $S\to\max\{S,1\}$)
-- statement:
--   In the PRG game (Definition 8.1) a random oracle $R:[N]\to\{0,1\}^m$ ($M=2^m$) is sampled uniformly. The adversary holds an $S$-qubit advice state $|\varphi_R\rangle$ depending arbitrarily on $R$ and a $w$-qubit workspace in $|0^w\rangle$. It receives either $R(x)$ for uniform $x\in[N]$ or a uniform $y\in\{0,1\}^m$, makes $T$ queries to $R$, and measures with $0\preceq\Pi\preceq I$.
--
--   There is a universal constant $C>0$ such that for all $S,T,m,w\ge0$, $N\ge1$, every such adversary and every advice map $R\mapsto|\varphi_R\rangle$ of unit vectors,
--   $$
--   \mathbb E_R\Big|\,\mathbb E_x\langle\varphi_R,0^w|\langle R(x)|A_R^\dagger\Pi A_R|R(x)\rangle|\varphi_R,0^w\rangle-\mathbb E_r\langle\varphi_R,0^w|\langle r|A_R^\dagger\Pi A_R|r\rangle|\varphi_R,0^w\rangle\Big|\,\le\,C\Big(\frac{T^2}{N}+\sqrt{\frac{\max\{S,1\}(T+1)}{N}}\Big),
--   $$
--   where $A_R=(O_RU)^T$.
--
--   This recovers the dependence $\sqrt{S(T+1)/N}$ of the best classical bound while allowing quantum advice and quantum queries.
--
--   Differences from the source:
--   - correction: O(T²/N + √(S(T+1)/N)) → C·(T²/N + √(max{S,1}(T+1)/N)); reason: as printed the bound is 0 at S = T = 0, but N = 1, m = 1, S = T = w = 0 and Π = |0⟩⟨0| on the challenge register give advantage E_R |1[R(0) = 0] − 1/2| = 1/2; the proof's moment order t = S/2 needs t ≥ 1
--   - reading: R : [N] → [M] → R : [N] → {0,1}^m with M = 2^m; reason: the page prepares the challenge as H|y⟩ with phases (−1)^{y·R(x)} (§8.1, p.31) and uses the XOR oracle on bit strings (§3.1)
--   - generalization: standard oracle |x,y⟩ ↦ |x, y ⊕ R(x)⟩ with one fixed unitary U → phase queries (−1)^{u·R(x)} through an arbitrary query map, distinct unitaries U_1, …, U_T; reason: the standard oracle is the phase oracle conjugated by Hadamards, which are absorbed into the neighbouring unitaries and Π; the page's form is a special case
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - encoding: maximum over advice |φ_R⟩ inside E_R → ∀ maps φ from oracles to unit vectors on [2^S]; reason: a bound for every map is a bound on E_R max
--   - encoding: seed set [N] → hypothesis 1 ≤ N; reason: excludes only the empty seed set, where E_x is undefined
--   - generalization: seed set [N] of a hash function on bit strings, N = 2^n (§3.1, p.11) → N any positive integer; reason: the case N = 2^n is included; the bound does not depend on the encoding of the seed
--   - encoding: a final unitary U_{T+1} before the measurement (§3.1) → no final unitary; Π is any operator with 0 ⪯ Π ⪯ I; reason: U_{T+1}†ΠU_{T+1} again satisfies 0 ⪯ · ⪯ I
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 8.2, p.30 (PDF p.33); §8.1, display (23), p.31 (PDF p.34)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_CompNonlocal_IsEffect
import Definitions.Def_PreprocOWS_Supplement_prgAdv
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 8.2 (Non-uniform security of PRG in QROM)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.30 (PDF p.33), with a minimal
correction at `S = 0`: the non-uniform security (with `S`-qubit advice and `T` queries) of PRG in
QROM is `O(T²/N + √(max{S,1}(T+1)/N))`; that is, the maximum distinguishing advantage is bounded by
that quantity. The page prints `√(S(T+1)/N)`.

**Formalization Note.** Correction: as printed the bound is `0` at `S = T = 0`, but `N = 1`, `m = 1`,
`w = 0` and `Π = |0⟩⟨0|` on the challenge register give advantage `E_R |1[R(0) = 0] − 1/2| = 1/2`;
the proof sets `t = S/2` and needs `t ≥ 1`. The `O(·)` is one universal `C > 0` chosen before
`S, T, N, m, w` and the adversary. `R : [N] → {0,1}^m` is uniform (`M = 2^m`); the advice `φ R` is
any unit vector on `S` qubits depending on `R` ("maximum" is `∀` advice maps); the measurement is
any `0 ⪯ Π ⪯ I`; the absolute value sits inside `E_R`. Queries are in phase form with a general
query map (see `PRGAlg`). -/
theorem theorem_8_2 : ∃ C : ℝ, 0 < C ∧ ∀ (S T N m w : ℕ), 1 ≤ N →
    ∀ A : PRGAlg S T N m w, CompNonlocal.IsEffect A.meas →
    ∀ φ : PRGOracle N m → Fin (2 ^ S) → ℂ, (∀ R, vnormSq (φ R) = 1) →
      avg (fun R => prgAdv A R (φ R)) ≤
        C * ((T : ℝ) ^ 2 / N + Real.sqrt ((max (S : ℝ) 1) * (T + 1) / N)) := by sorry

end PreprocOWS.Supplement

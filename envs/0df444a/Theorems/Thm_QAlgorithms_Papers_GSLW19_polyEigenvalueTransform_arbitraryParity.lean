-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GSLW19_polyEigenvalueTransform_arbitraryParity
-- name    : QAlgorithms.Papers.GSLW19.polyEigenvalueTransform_arbitraryParity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:47:48.187991+00:00
-- url     : https://prove2.me/theorems/7b225e25-1bfc-4f30-a97d-a1630603a8ae
-- title:
--   GSLW Theorem 56: polynomial eigenvalue transformation of arbitrary parity
-- statement:
--   This is the polynomial eigenvalue transformation theorem of Gilyén, Su, Low and Wiebe, which removes the parity constraint of quantum singular value transformation at the price of a factor $1/2$.
--
--   For an $s$-qubit operator $A$, real numbers $\alpha>0$, $\varepsilon\ge 0$ and $a\in\mathbb N$, an $(a+s)$-qubit unitary $U$ is an $(\alpha,a,\varepsilon)$-block-encoding of $A$ if
--
--   $$
--   \big\|A-\alpha\,(\langle 0|^{\otimes a}\otimes I)\,U\,(|0\rangle^{\otimes a}\otimes I)\big\|\le\varepsilon ,
--   $$
--
--   where $\|\cdot\|$ is the operator norm and the ancilla register comes first.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $s,a,d\in\mathbb N$, let $\delta\ge 0$, and let $P\in\mathbb R[x]$ be a polynomial of degree at most $d$ with $|P(x)|\le \tfrac12$ for all $x\in[-1,1]$. Then there exist $w\in\mathbb N$ and a quantum circuit $\tilde U$ on $(a+2)+s+w$ qubits, built from one- and two-qubit gates and calls to a black box $U$ on $a+s$ qubits, with
--
--   1. at most $d$ uncontrolled applications of $U$ or $U^\dagger$,
--   2. at most one controlled application of the black box,
--   3. at most $C(a+1)\max(d,1)$ other gates,
--
--   such that for every $\alpha>0$, $\varepsilon\ge 0$, every Hermitian $s$-qubit matrix $A$ with $\|A\|\le\alpha$ and every $(\alpha,a,\varepsilon)$-block-encoding $U$ of $A$, the circuit $\tilde U$ (with the last $w$ qubits as clean ancillas, started and returned exactly in $|0\rangle$) implements a unitary $V$ on $(a+2)+s$ qubits that is a
--
--   $$
--   \Big(1,\;a+2,\;4d\sqrt{\varepsilon/\alpha}+\delta\Big)\text{-block-encoding of } P(A/\alpha).
--   $$
--
--   This theorem is the workhorse for implementing smooth functions of Hermitian matrices (Hamiltonian simulation, matrix inversion, Gibbs sampling) through block-encodings.
--
--   **Formalization Note** The circuit is chosen before $\alpha,\varepsilon,A,U$, so it depends only on $s,a,d,P,\delta$. The source's $O((a+1)d)$ is encoded with $\max(d,1)$ since a constant polynomial still needs a few gates. The source's last sentence (classical computability of the circuit description in time $\mathrm{poly}(d,\log(1/\delta))$) is not formalized, because the source fixes no bit model for the real coefficients of $P$. The controlled query may be controlled-$U$ or controlled-$U^\dagger$. The hypothesis $\|A\|\le\alpha$ corrects the printed statement: the source's proof uses Lemma 22, which needs $\|A/\alpha\|\le 1$, and without it the printed statement fails (e.g. $A=[2]$, $U=[1]$, $\alpha=\varepsilon=1$, $P=T_8/2$, $d=8$).
--
--   **Correction to the printed source.**
--
--   Printed: Suppose that U is an (α, a, ε)-encoding of a Hermitian matrix A (no condition ‖A‖ ≤ α; Definition 43 only forces ‖A‖ ≤ α + ε).
--
--   Corrected: Added the hypothesis specNorm A ≤ α, i.e. ‖A/α‖ ≤ 1.
--
--   Reason: The proof (p.49) applies Lemma 22 (p.23), which requires both matrices to have operator norm at most 1. Without it the statement is false: s = a = 0, α = ε = 1, A = [2], U = [1] is a (1, 0, 1)-encoding of A; with P = T_8/2, d = 8, δ = 0 one gets P(A/α) = T_8(2)/2 ≈ 9408, while every block of a unitary has norm ≤ 1 and the claimed error is 32.
-- source:
--   Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics (Gilyén, Su, Low, Wiebe), arXiv:1806.01838v1, Theorem 56, PDF p. 48. https://arxiv.org/abs/1806.01838v1 . PDF SHA-256: 0326a3de56b10c9805074031a827b1ac4c5ee526c5ad362096adfbacc261c60d.

import Definitions.Def_QAlgorithms_Defs_CircuitResources
set_option autoImplicit false

namespace QAlgorithms.Papers.GSLW19

open QAlgorithms

/-- **GSLW Theorem 56** (PDF p.48), polynomial eigenvalue transformation of arbitrary parity.

Suppose `U` is an `(α, a, ε)`-encoding of a Hermitian `s`-qubit matrix `A`. If `δ ≥ 0` and
`P ∈ ℝ[x]` is a degree-`d` polynomial with `|P(x)| ≤ 1/2` on `[−1, 1]`, then there is a circuit
`Ũ` which is a `(1, a + 2, 4d√(ε/α) + δ)`-encoding of `P(A/α)`, made of `d` applications of `U`
and `U†`, a single application of controlled-`U` and `O((a + 1)d)` other one- and two-qubit
gates.

Encoding choices: "degree-`d`" is `natDegree P ≤ d` and the use counts are upper bounds; the
circuit depends only on `s, a, d, P, δ` (never on `α, ε, A, U`); the `O((a+1)d)` bound is
`C · (a + 1) · max d 1` with an absolute `C` (at `d = 0` the literal bound `0` is impossible,
since the final circuit has Hadamards on the two new ancillas); the single controlled query may
be controlled-`U` or controlled-`U†` (the count does not fix the adjoint flag); `α > 0` (the
source's `α ∈ ℝ₊`, needed for `A/α`).

**Correction** (trap 30). Printed: no norm condition on `A` beyond what the encoding forces
(`‖A‖ ≤ α + ε`, p.41). Changed: the hypothesis `‖A‖ ≤ α` (`specNorm A ≤ α`) is added. Why: the
proof (p.49) applies Lemma 22 (p.23), which requires `‖A/α‖ ≤ 1`; without it the printed statement
is false: `s = a = 0`, `α = ε = 1`, `A = [2]`, `U = [1]` (a `(1, 0, 1)`-encoding of `A`),
`P = T₈/2`, `d = 8`, `δ = 0` gives `P(A/α) = T₈(2)/2 ≈ 9408`, while every block of a unitary has
norm `≤ 1` and the claimed error is `32`. **Not stated**: the final sentence, that a description of
the circuit is classically computable in time `O(poly(d, log(1/δ)))`, because `P` has real
coefficients and the source fixes no bit model for them. -/
theorem polyEigenvalueTransform_arbitraryParity :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s a d : ℕ) (P : Polynomial ℝ) (δ : ℝ), 0 ≤ δ → P.natDegree ≤ d →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) →
        ∃ (w : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + s) (a + 2 + s + w)),
          c.plainQueryCount 0 ≤ d ∧ c.controlledQueryCount 0 ≤ 1 ∧
          (c.gateCount : ℝ) ≤ C * ((a : ℝ) + 1) * (max d 1 : ℕ) ∧
          ∀ (α ε : ℝ) (A : Matrix (Qubits s) (Qubits s) ℂ)
            (U : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ),
            0 < α → 0 ≤ ε → A.IsHermitian → specNorm A ≤ α →
            IsQubitBlockEncoding a s U α ε A →
            ∃ V : Matrix (Qubits (a + 2 + s)) (Qubits (a + 2 + s)) ℂ,
              ImplementsWithCleanAncillas (c.unitary fun _ => U) V ∧
              IsQubitBlockEncoding (a + 2) s V 1 (4 * d * Real.sqrt (ε / α) + δ)
                (Polynomial.aeval ((α : ℂ)⁻¹ • A) P) := by
  sorry


end QAlgorithms.Papers.GSLW19

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GAW19_probOracle_to_phaseOracle
-- name    : QAlgorithms.Papers.GAW19.probOracle_to_phaseOracle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:47:21.13952+00:00
-- url     : https://prove2.me/theorems/cb0bb292-eadc-4a09-a94e-0f99ca9a3388
-- title:
--   GAW Theorem 14: a probability oracle yields an ε-approximate phase oracle with O(log(1/ε)) queries
-- statement:
--   This is the conversion of a probability oracle into an approximate phase oracle (Gilyén–Arunachalam–Wiebe, Theorem 14).
--
--   Let $X$ be a finite set and $\mathcal H$ the Hilbert space with orthonormal basis $\{|x\rangle : x\in X\}$. A *probability oracle* for $p : X\to[0,1]$ with an $n$-qubit auxiliary register is a unitary $U_p$ on $\mathcal H\otimes\mathbb C^{2^n}$ with
--   $$U_p|x\rangle|0\rangle^{\otimes n} = |x\rangle\otimes\Big(\sqrt{p(x)}\,|\psi_{\mathrm{good}}(x)\rangle|1\rangle + \sqrt{1-p(x)}\,|\psi_{\mathrm{bad}}(x)\rangle|0\rangle\Big)$$
--   for some normalized states $\psi_{\mathrm{good}}(x),\psi_{\mathrm{bad}}(x)$ (the flag is the last qubit). A *phase oracle* for $p$ on an auxiliary register is a unitary $O_p$ with $O_p|x\rangle|0\rangle = e^{ip(x)}|x\rangle|0\rangle$ for all $x\in X$.
--
--   There is an absolute constant $C>0$ such that for every $\varepsilon\in(0,1/3)$, every finite $X$ and every $n\ge1$ there are a number $a\le C\log\log(1/\varepsilon)$ of extra qubits and a quantum circuit $O$ on $\mathcal H\otimes\mathbb C^{2^{n+a}}$, built from input-independent unitaries and at most $C\log(1/\varepsilon)$ (uncontrolled) applications of $U_p$ and $U_p^\dagger$, such that for every $p$, every probability oracle $U_p$ for $p$, every phase oracle $O_p$ for $p$ on $n+a$ auxiliary qubits, and every unit vector $|\psi\rangle\in\mathcal H$,
--   $$\big\| O|\psi\rangle|0\rangle^{\otimes(n+a)} - O_p|\psi\rangle|0\rangle^{\otimes(n+a)}\big\| \le \varepsilon .$$
--
--   This shows that the probability oracles arising from parametrized quantum circuits can be used wherever a phase oracle is needed, at only logarithmic overhead in the precision.
--
--   **Formalization Note** The circuit is fixed before $p$ and $U_p$; the source's $n$-qubit auxiliary register is written $n=m+1$. The source's "for all $|\psi\rangle\in\mathcal H$" is read for unit vectors, as in the proof.
-- source:
--   Optimizing quantum optimization algorithms via faster quantum gradient computation (Gilyén, Arunachalam, Wiebe), arXiv:1711.00465v3, Theorem 14, PDF p. 18. https://arxiv.org/abs/1711.00465v3 . PDF SHA-256: 4b76edbf6d3c29bbb48102f8108e19d938981759540f741e091370c9817c4e63.

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
set_option autoImplicit false

namespace QAlgorithms.Papers.GAW19

universe u

/-- GAW p.18, Theorem 14 (probability oracle to approximate phase oracle). Let `p : X → [0, 1]` and
let `U_p` be a probability oracle for `p` with an `n`-qubit auxiliary space (`n = m + 1`, the flag
being the last qubit). For `ε ∈ (0, 1/3)` there is a circuit `O` with `a = O(log log(1/ε))` extra
qubits and `O(log(1/ε))` applications of `U_p` and `U_p†` such that for every phase oracle `O_p`
for `p` and every unit `ψ ∈ H`,
`‖O |ψ⟩|0⟩^{⊗(n+a)} − O_p |ψ⟩|0⟩^{⊗(n+a)}‖ ≤ ε`.

The circuit depends only on `ε`, `X` and `n`, never on `p` or `U_p`; its oracle applications are
uncontrolled (footnote 13: controlled `G_U` only controls the reflections). "For all `|ψ⟩ ∈ H`" is
read as unit `ψ` (the proof, eqs. (18)–(19), bounds the error for normalized `ψ`). -/
theorem probOracle_to_phaseOracle :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      ∀ (X : Type u) [Fintype X] [DecidableEq X] (m : ℕ),
        ∃ a : ℕ, (a : ℝ) ≤ C * Real.log (Real.log (1 / ε)) ∧
          ∃ c : PhaseQueryCircuit X Unit (m + 1) a,
            (∀ s ∈ c, ∀ (r : Unit) (adj : Bool) (b : Fin a), s ≠ .query r adj (some b)) ∧
            (c.queryCount : ℝ) ≤ C * Real.log (1 / ε) ∧
            ∀ (p : X → ℝ) (Up : Matrix (X × Qubits (m + 1)) (X × Qubits (m + 1)) ℂ),
              IsGAWProbabilityOracle Up p →
              ∀ Op : Matrix (X × Qubits (m + 1 + a)) (X × Qubits (m + 1 + a)) ℂ,
                IsGAWPhaseOracle (fun _ => false) Op p →
                ∀ ψ : EuclideanSpace ℂ X, ‖ψ‖ = 1 →
                  ‖act (c.unitary fun _ => Up) (tensorVec ψ (ket fun _ => false)) -
                    act Op (tensorVec ψ (ket fun _ => false))‖ ≤ ε := by
  sorry




end QAlgorithms.Papers.GAW19

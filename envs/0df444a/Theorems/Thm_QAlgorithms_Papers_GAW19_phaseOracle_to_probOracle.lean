-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GAW19_phaseOracle_to_probOracle
-- name    : QAlgorithms.Papers.GAW19.phaseOracle_to_probOracle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:47:17.070852+00:00
-- url     : https://prove2.me/theorems/1ab43a1f-95e2-462c-a477-5e30f737921d
-- title:
--   GAW Lemma 16: a phase oracle yields a probability oracle with O(log(1/ε)/δ) queries
-- statement:
--   This is the conversion of a phase oracle into a probability oracle (Gilyén–Arunachalam–Wiebe, Lemma 16).
--
--   Let $X$ be a finite set, $\mathcal H$ the Hilbert space with orthonormal basis $\{|x\rangle : x\in X\}$, and let $O_p$ be a phase oracle for $p : X\to\mathbb R$ on $\mathcal H\otimes\mathbb C^{2^w}$, i.e. a unitary with $O_p|x\rangle|0\rangle^{\otimes w}=e^{ip(x)}|x\rangle|0\rangle^{\otimes w}$ for all $x\in X$.
--
--   There is an absolute constant $C>0$ such that for all $\varepsilon,\delta\in(0,1/2)$, every finite $X$ and every $w$ there are $k$ and a quantum circuit $U_p$ on $\mathcal H\otimes\mathbb C^{2^{k+1}}$, built from input-independent unitaries and at most $C\log(1/\varepsilon)/\delta$ invocations of $O_p$, $O_p^\dagger$ or their controlled versions, such that for every $p : X\to[\delta,1-\delta]$, every phase oracle $O_p$ for $p$ and every $x\in X$ there are $p'(x)\in[0,1]$ and a unit vector $|\Phi^\perp\rangle$ with
--   $$U_p|x\rangle|0\rangle^{\otimes k}|0\rangle = |x\rangle\otimes\Big(\sqrt{p'(x)}\,|0\rangle^{\otimes k}|0\rangle + \sqrt{1-p'(x)}\,|\Phi^\perp\rangle|1\rangle\Big), \qquad \big|\sqrt{p'(x)}-\sqrt{p(x)}\big|\le\varepsilon .$$
--
--   Together with Theorem 14 this shows that phase and probability oracles are interconvertible with logarithmic overhead in the precision when the probabilities are bounded away from $0$ and $1$.
--
--   **Formalization Note** The register $|0\rangle^{\otimes k}$ consists of the $w$ auxiliary qubits of $O_p$ and $a$ further qubits ($k=w+a$); the last qubit is the flag. The source's "for every $x\in\mathbb R^n$" is read as $x\in X$, the domain of $p$.
-- source:
--   Optimizing quantum optimization algorithms via faster quantum gradient computation (Gilyén, Arunachalam, Wiebe), arXiv:1711.00465v3, Lemma 16, PDF p. 21. https://arxiv.org/abs/1711.00465v3 . PDF SHA-256: 4b76edbf6d3c29bbb48102f8108e19d938981759540f741e091370c9817c4e63.

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
set_option autoImplicit false

namespace QAlgorithms.Papers.GAW19

universe u


/-- GAW p.21, Lemma 16 (phase oracle to probability oracle; proof in Appendix B, pp.55–57). Let
`ε, δ ∈ (0, 1/2)` and `p : X → [δ, 1 − δ]`. Given a phase oracle `O_p` (with any `w`-qubit
auxiliary register), `O(log(1/ε)/δ)` invocations of the (controlled) `O_p` and `O_p†` implement
`U_p : |x⟩|0⟩^{⊗k}|0⟩ ↦ |x⟩ ⊗ (√p′(x) |0⟩^{⊗k}|0⟩ + √(1 − p′(x)) |Φ^⊥⟩|1⟩)` with
`|√p′(x) − √p(x)| ≤ ε` for every `x ∈ X`.

Here `k = w + a`: the register `|0⟩^{⊗k}` holds the oracle's `w` auxiliary qubits and `a` extra
ones, and the last qubit is the flag. The source's "for every `x ∈ ℝⁿ`" is a typo for `x ∈ X` (the
lemma's domain). The displayed map (good amplitude on `|0^k⟩` with flag `0`) is stated literally;
`|Φ^⊥⟩` is a unit vector. The circuit is fixed before `p` and `O_p` (trap Q2). -/
theorem phaseOracle_to_probOracle :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
      ∀ (X : Type u) [Fintype X] [DecidableEq X] (w : ℕ),
        ∃ (a : ℕ) (c : PhaseQueryCircuit X Unit w (a + 1)),
          (c.queryCount : ℝ) ≤ C * Real.log (1 / ε) / δ ∧
          ∀ p : X → ℝ, (∀ x, δ ≤ p x ∧ p x ≤ 1 - δ) →
            ∀ Op : Matrix (X × Qubits w) (X × Qubits w) ℂ,
              IsGAWPhaseOracle (fun _ => false) Op p →
              ∀ x : X, ∃ p' : ℝ, 0 ≤ p' ∧ p' ≤ 1 ∧ |Real.sqrt p' - Real.sqrt (p x)| ≤ ε ∧
                ∃ Φ : EuclideanSpace ℂ (Qubits (w + a)), ‖Φ‖ = 1 ∧
                  act (c.unitary fun _ => Op) (ket (x, fun _ => false)) =
                    (tensorVec (ket x)
                      ((Real.sqrt p' : ℂ) • snocQubit (zeroKet (w + a)) false +
                        (Real.sqrt (1 - p') : ℂ) • snocQubit Φ true) :
                      EuclideanSpace ℂ (X × Qubits (w + (a + 1)))) := by
  sorry



end QAlgorithms.Papers.GAW19

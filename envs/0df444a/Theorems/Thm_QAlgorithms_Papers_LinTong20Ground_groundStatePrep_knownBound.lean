-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LinTong20Ground_groundStatePrep_knownBound
-- name    : QAlgorithms.Papers.LinTong20Ground.groundStatePrep_knownBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:03:58.505992+00:00
-- url     : https://prove2.me/theorems/d243ae6b-cc99-4b1d-ba7c-46f37fdfe8cf
-- title:
--   Lin–Tong Theorem 6: ground state preparation with an a priori ground energy bound
-- statement:
--   This is the ground state preparation theorem of Lin and Tong for the case where an upper bound on the ground energy is known.
--
--   Let $N = 2^n$ and let $H \in \mathbb{C}^{N\times N}$ be Hermitian with eigenvalues $\lambda_0 \le \lambda_1 \le \cdots \le \lambda_{N-1}$ and a ground state $|\psi_0\rangle$ (a unit eigenvector for $\lambda_0$). Access is through two unitary oracles: an $(\alpha, m, 0)$-block-encoding $U_H$ of $H$, i.e. an $(m+n)$-qubit unitary with $H = \alpha\,(\langle 0^m| \otimes I)\,U_H\,(|0^m\rangle \otimes I)$, and an $n$-qubit unitary $U_I$ preparing $|\phi_0\rangle = U_I|0^n\rangle$. For known parameters $\alpha \ge 0$, $\Delta > 0$, $\mu \in \mathbb{R}$, $\gamma \in (0,1]$ the promises are
--
--   1. (P1) $|\langle \phi_0|\psi_0\rangle| \ge \gamma$;
--   2. (P2) $\lambda_0 \le \mu - \Delta/2 < \mu + \Delta/2 \le \lambda_1$.
--
--   There are absolute constants $C, c > 0$ such that for every $n, m, \alpha, \Delta, \mu, \gamma$ and every $\epsilon \in (0,1)$ there is a quantum circuit of one- and two-qubit gates with oracle calls (plain, inverse or controlled) to $U_H$ and $U_I$, on $n + w$ qubits started in $|0^{n+w}\rangle$, together with a set of accepted outcomes of its $w$ ancilla qubits, such that
--
--   $$
--   \#U_H \le C\,\frac{\alpha}{\gamma\Delta}\log\frac{1}{\gamma\epsilon},\qquad \#U_I \le \frac{C}{\gamma},\qquad n + w \le C(n+m+1),\qquad \#\text{gates} \le C\,(m+1)\frac{\alpha}{\gamma\Delta}\log\frac{1}{\gamma\epsilon},
--   $$
--
--   and, for every instance $(H, U_H, U_I)$ satisfying (P1) and (P2), measuring the ancillas gives an accepted outcome with probability at least $c$, and for every accepted outcome the post-measurement state $|\tilde\psi\rangle$ of the system register has fidelity $|\langle \psi_0|\tilde\psi\rangle| \ge 1 - \epsilon$.
--
--   The circuit depends only on the known parameters, not on the instance. The query cost is logarithmic in the inverse precision, which the paper shows to be essentially optimal in $\gamma$ and $\Delta$.
--
--   **Formalization Note** The source writes $O(n+m)$ qubits and $O(\frac{m\alpha}{\gamma\Delta}\log\frac{1}{\gamma\epsilon})$ gates; these are stated with $n+m+1$ and $m+1$, since at $n=m=0$ (resp. $m=0$) the literal bound is zero while the construction needs ancillas and Hadamard gates (the paper's own Theorem 1 gives $O((m+1)\ell)$ gates). The constant success probability is the proof's reading of the theorem ("the procedure succeeds with some constant probability"). Fidelity is $|\langle x|y\rangle|$, as in the paper's footnote 1.
-- source:
--   Near-optimal ground state preparation (Lin, Tong), arXiv:2002.12508v3, Theorem 6, PDF p. 7. https://arxiv.org/abs/2002.12508v3 . PDF SHA-256: 2e960ca1d65389916d9b2fd9e47a0e3531771d367be7c15a3ccc8ca48c0f4b07.

import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Papers_LinTong20Ground_Model
set_option autoImplicit false

namespace QAlgorithms.Papers.LinTong20Ground

open QAlgorithms




/-- **LT-gs Theorem 6** (PDF p.7), ground state preparation with an a priori ground energy bound.

Suppose `H = Σ_k λ_k |ψ_k⟩⟨ψ_k| ∈ ℂ^{N×N}` (`λ_k ≤ λ_{k+1}`) is given through its
`(α, m, 0)`-block-encoding `U_H`, the initial state `|φ₀⟩` is prepared by `U_I`, and the promises
(P1) `|⟨φ₀|ψ₀⟩| ≥ γ` and (P2) `λ₀ ≤ μ − Δ/2 < μ + Δ/2 ≤ λ₁` hold. Then the ground state `|ψ₀⟩`
can be prepared to fidelity `1 − ε` with `O((α/(γΔ)) log(1/(γε)))` queries to `U_H`, `O(1/γ)`
queries to `U_I`, `O(n + m)` qubits and `O((mα/(γΔ)) log(1/(γε)))` other one- and two-qubit
gates.

Encoding choices.
* The circuit, its number `w` of ancillas and its success predicate `good` on ancilla outcomes are
  chosen from the known data `n, m, α, Δ, μ, γ, ε` only, before `H, U_H, U_I` (trap Q2; p.6:
  "for some known `γ > 0`, `μ`, and `Δ`"). It runs on `|0^{n+w}⟩`, system register the first `n`
  wires; the ancillas are measured, and outcome `a` with `good a` is success.
* "Prepared … with the following costs" is read through the proof (p.7: "the procedure succeeds
  with some constant probability"): one absolute constant `c > 0` lower-bounds the success
  probability, and on every successful outcome the post-measurement system state
  `v_a / ‖v_a‖` has fidelity `|⟨ψ₀|v_a⟩| / ‖v_a‖ ≥ 1 − ε` (stated without division).
* `O(·)` is one absolute constant `C`, quantified before everything (trap 8). The source's `O` is
  plain (its `Õ`, footnote 2, is not used in Theorem 6, and the proof gives no log factors).
* (P2) is stated without indexing `λ₁` directly: `λ₀ ≤ μ − Δ/2`, `Δ > 0`, and every eigenvalue of
  index `k ≥ 1` is `≥ μ + Δ/2`. (P1) uses the ground state `ψ₀` (unique up to phase under (P2), so
  the overlap and the fidelity do not depend on the choice). `0 < ε < 1` (fidelity `1 − ε`).
* The known parameters carry the constraints the instances force (so that the cost bounds, which
  are fixed before any instance, are not negative on parameter values that admit no instance):
  `0 ≤ α` (the block-encoding's normalization), `0 < γ ≤ 1` (an overlap of unit vectors, (P1)).
  With them `γε < 1`, so `log(1/(γε)) > 0`.

**Corrections** (trap 30). Printed: `O(n + m)` qubits and `O((mα/(γΔ)) log(1/(γε)))` gates.
Changed: `n + w ≤ C(n + m + 1)` and `(m + 1)` in place of `m`. Why: at `n = m = 0` the printed
qubit bound is `0`, and at `m = 0` the printed gate bound is `0`, while the construction needs
`m + 3` ancillas and Hadamard gates (the paper's own Theorem 1, p.3, gives `O((m + 1)ℓ)` gates). -/
theorem groundStatePrep_knownBound :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) (α Δ μ γ ε : ℝ), 0 ≤ α → 0 < Δ → 0 < γ → γ ≤ 1 → 0 < ε → ε < 1 →
        ∃ (w : ℕ) (circ : OracleCircuit oneTwoQubitGateSet ![m + n, n] (n + w))
          (good : Qubits w → Bool),
          ((n + w : ℕ) : ℝ) ≤ C * ((n : ℝ) + m + 1) ∧
          (circ.queryCount 0 : ℝ) ≤ C * (α / (γ * Δ)) * Real.log (1 / (γ * ε)) ∧
          (circ.queryCount 1 : ℝ) ≤ C * (1 / γ) ∧
          (circ.gateCount : ℝ) ≤ C * ((m : ℝ) + 1) * (α / (γ * Δ)) * Real.log (1 / (γ * ε)) ∧
          ∀ (H : Matrix (Qubits n) (Qubits n) ℂ)
            (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
            (UI : Matrix (Qubits n) (Qubits n) ℂ) (ψ0 : EuclideanSpace ℂ (Qubits n)),
            H.IsHermitian → IsQubitBlockEncoding m n UH α 0 H →
            UI ∈ Matrix.unitaryGroup (Qubits n) ℂ →
            IsGroundState H ψ0 →
            -- (P1)
            γ ≤ ‖inner ℂ ψ0 (act UI (zeroKet n))‖ →
            -- (P2)
            minEigenvalue H ≤ μ - Δ / 2 →
            (∀ k : Fin (Fintype.card (Qubits n)), (k : ℕ) ≠ 0 → μ + Δ / 2 ≤ ascEigenvalues H k) →
            c ≤ probEvent (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w)))
                (fun z => good (qubitsAppendEquiv n w z).2 = true) ∧
              ∀ a : Qubits w, good a = true →
                (1 - ε) * ‖ancillaBranch (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w))) a‖ ≤
                  ‖inner ℂ ψ0
                    (ancillaBranch (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w))) a)‖ := by
  sorry

end QAlgorithms.Papers.LinTong20Ground

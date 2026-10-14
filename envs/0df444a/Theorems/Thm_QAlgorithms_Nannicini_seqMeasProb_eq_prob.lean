-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_seqMeasProb_eq_prob
-- name    : QAlgorithms.Nannicini.seqMeasProb_eq_prob
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:11.545435+00:00
-- url     : https://prove2.me/theorems/cc42db0c-9397-4ff5-8ae7-1527ed5db6e9
-- title:
--   Measuring all qubits one at a time, in any order, yields j with probability |α_j|²
-- statement:
--   Let $|\psi\rangle=\sum_{\vec\jmath\in\{0,1\}^q}\alpha_j|\vec\jmath\rangle$ be a $q$-qubit quantum state (a unit vector). A single-qubit measurement gate on qubit $k$ (Postulate 3) outputs $x\in\{0,1\}$ with probability $\Pr(Q_k=x)=\sum_{\vec\jmath:\vec\jmath_k=x}|\alpha_j|^2$, after which the state collapses to $\sum_{\vec\jmath:\vec\jmath_k=x}\alpha_j\big/\sqrt{\sum_{\vec\ell:\vec\ell_k=x}|\alpha_\ell|^2}\;|\vec\jmath\rangle$. Let $\sigma$ be any ordering of the $q$ qubits, and measure the qubits one at a time in the order $\sigma(1),\sigma(2),\dots,\sigma(q)$, each measurement acting on the state left by the previous ones. Then for every $\vec\jmath\in\{0,1\}^q$, the probability that the outcomes are $\vec\jmath_{\sigma(1)},\dots,\vec\jmath_{\sigma(q)}$ is
--
--   $$
--   \Pr\big(Q_1=\vec\jmath_1,\dots,Q_q=\vec\jmath_q\big)=|\alpha_j|^2 .
--   $$
--
--   Thus measuring all qubits sequentially with single-qubit measurement gates is the same as one measurement of the whole register in the computational basis.
--
--   **Formalization Note** The sequential probability is the product of the successive conditional outcome probabilities, each computed on the collapsed state. When an intermediate outcome has probability zero, the collapse formula divides by zero (Lean returns the zero vector); the product is then zero, as is $|\alpha_j|^2$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 19, Proposition 1.27. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini p.19, Proposition 1.27: for a `q`-qubit state `|ψ⟩ = ∑_j α_j |j⟩`, measuring the
`q` qubits one at a time with the single-qubit measurement gate of Postulate 3 (outcome
probability, then collapse and renormalization), in any order, yields the string `j` with
probability `|α_j|²`. The order is a permutation `σ` of the qubits: qubit `σ 0` is measured
first, then `σ 1`, and so on. -/
theorem seqMeasProb_eq_prob {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (σ : Equiv.Perm (Fin q)) (j : Qubits q) :
    seqMeasProb ψ (List.ofFn fun i => σ i) j = prob ψ j := by
  sorry



end QAlgorithms.Nannicini

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_ServedioGortler01_quantumPAC_separation
-- name    : QAlgorithms.Papers.ServedioGortler01.quantumPAC_separation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:05:15.664883+00:00
-- url     : https://prove2.me/theorems/b3d3ee4d-fd2f-46ea-b7e8-695c8dc102f4
-- title:
--   Factoring hardness separates efficient quantum and classical PAC learning
-- statement:
--   A Blum integer is $N=pq$ with $p\ne q$ $\ell$-bit primes, $p\equiv q\equiv 3\pmod 4$. Assume that no polynomial-time classical randomized algorithm factors a uniformly random Blum integer with non-negligible success probability: for every such algorithm $A$ and every polynomial $q$, for all sufficiently large $\ell$,
--
--   $$
--   \Pr_{N}\big[A(N)\text{ outputs a nontrivial factor of }N\big]<\frac{1}{q(\ell)+1}.
--   $$
--
--   Then there is a concept class $\mathcal C=\bigcup_{n\ge1}C_n$, $C_n$ a set of Boolean functions on $\{0,1\}^n$, such that:
--
--   1. $\mathcal C$ is efficiently quantum PAC learnable: for all $n\ge1$ and accuracy and confidence parameters there is a quantum network over $\{H,T,\mathrm{CNOT}\}$ whose $T$ quantum example gates $QEX(c,\mathcal D):|0^n,0\rangle\mapsto\sum_x\sqrt{\mathcal D(x)}|x,c(x)\rangle$ sit at the bottom of the circuit, of size polynomial in $n,1/\varepsilon,1/\delta$, which for every $c\in C_n$ and every distribution $\mathcal D$ on $\{0,1\}^n$ outputs, with probability at least $1-\delta$, a Boolean circuit $h$ with $\Pr_{x\sim\mathcal D}[h(x)\ne c(x)]\le\varepsilon$;
--   2. $\mathcal C$ is not efficiently classically PAC learnable: no probabilistic Turing machine running in time polynomial in $n,1/\varepsilon,1/\delta$ achieves the same guarantee from independent labelled examples $\langle x,c(x)\rangle$, $x\sim\mathcal D$.
--
--   This shows that the information-theoretic equivalence of quantum and classical PAC learning does not extend to computationally efficient learning, under a standard cryptographic assumption.
--
--   **Formalization Note** $\varepsilon=1/a$ and $\delta=1/b$ with integers $a,b\ge2$, and polynomials in $(n,1/\varepsilon,1/\delta)$ are polynomials in $n+a+b$; this is equivalent up to polynomial factors. As in the source, the quantum learner is a non-uniform family of networks while the classical learner is a uniform machine.
-- source:
--   Quantum versus Classical Learnability (Servedio, Gortler), arXiv:quant-ph/0007036v1, Observation 17, PDF p. 12. https://arxiv.org/abs/quant-ph/0007036v1 . PDF SHA-256: a8c814c9ef94c99ab58d4eeb5d4e98cec6f2cc24c6535e81e6ee3722ae1fdea3.

import Definitions.Def_QAlgorithms_Defs_LearningSeparation
set_option autoImplicit false

namespace QAlgorithms.Papers.ServedioGortler01

open QAlgorithms.Learning


/-- SG, Observation 17 (p.12), with the hardness hypothesis of p.11.

If no polynomial-time classical randomized algorithm factors a uniformly random Blum integer
`N = pq` (`p ≠ q` `ℓ`-bit primes, `p ≡ q ≡ 3 (mod 4)`) with non-negligible success probability
(`FactoringBlumHard`), then there is a concept class `C = (C_n)_n` that is efficiently quantum PAC
learnable (a family of `{H, T, CNOT}` networks with QEX gates at the bottom, of size polynomial in
`n, 1/ε, 1/δ`, outputting a circuit that is an `ε`-approximator of `c` under `D` with probability
`≥ 1 − δ`, for every `c ∈ C_n` and every distribution `D`) but not efficiently classically PAC
learnable (no polynomial-time probabilistic Turing machine does the same from `EX(c, D)`).

Accuracy and confidence enter as `ε = 1/a`, `δ = 1/b` with integers `a, b ≥ 2`, which is
equivalent to the source's real `ε, δ ∈ (0, 1)` up to polynomial factors.

As in the source (p.10), the quantum learner is a non-uniform family of networks while the
classical learner is a uniform machine. -/
theorem quantumPAC_separation (hfact : FactoringBlumHard) :
    ∃ C : (n : ℕ) → Set (Qubits n → Bool),
      EffQuantumPACLearnable C ∧ ¬ EffClassicalPACLearnable C := by
  sorry


end QAlgorithms.Papers.ServedioGortler01

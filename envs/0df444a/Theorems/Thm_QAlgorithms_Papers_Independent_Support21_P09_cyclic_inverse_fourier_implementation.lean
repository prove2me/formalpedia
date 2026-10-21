-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_cyclic_inverse_fourier_implementation
-- name    : QAlgorithms.Papers.Independent.Support21.P09.cyclic_inverse_fourier_implementation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:47:47.348+00:00
-- url     : https://prove2.me/theorems/5bcbeee9-6f55-405c-9ed9-09158d74ddcd
-- title:
--   Inverse Fourier implementation of cyclic POVMs
-- statement:
--   For integers $1\le d\le n$, let $M_{rj}=e^{2\pi i rj/n}/\sqrt n$, with $0\le r<d$ and $0\le j<n$, and let $F_n$ be the same positive-sign Fourier matrix with all $n$ rows. Its nonzero column effects form a POVM, and $F_n\in U(n)$ has $M$ as its first $d$ rows. For every density matrix $\rho$ and outcome $j$,
--
--   $$
--   [F_n^\dagger(\rho\oplus0_{n-d})F_n]_{jj}=\operatorname{tr}(\rho M_{:,j}M_{:,j}^\dagger).
--   $$
--
--   Moreover, there is one polynomial $p\in\mathbb N[x]$ such that for every $k\ge0$ the exact transform $F_{2^k}^\dagger$ has a circuit on $k$ qubits, using arbitrary one- and two-qubit unitary gates, of size at most $p(k)$. The polynomial and circuit are independent of the input state and of which initial segment $d\le2^k$ is used. The seed has squared norm $d/n$; the implementation is the adjoint of the positive Fourier transform.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 15, §6.1: inverse Fourier implementation of cyclic POVMs

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.14–15, §6.1: inverse positive Fourier transform implements the cyclic POVM.
The polynomial is chosen before the dyadic size and hence also before any input state. -/
theorem cyclic_inverse_fourier_implementation :
    (∀ d n : ℕ, ∀ hd : 0 < d, ∀ hdn : d ≤ n,
      RankOnePOVM (cyclicColumns d n) ∧
      qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (∀ i j, qftMatrix n (Fin.castLE hdn i) j = cyclicColumns d n i j) ∧
      ImplementsPOVM (cyclicColumns d n) (qftMatrix n).conjTranspose (Fin.castLE hdn)) ∧
    (∃ p : Polynomial ℕ, ∀ k : ℕ, ∃ circ : Circuit elementaryGates k,
      circ.size ≤ p.eval k ∧ circ.unitary = (qftQubits k).conjTranspose) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P10_qubit_register_space
-- name    : QAlgorithms.Papers.Independent.Next46.P10.qubit_register_space
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:02:13.152984+00:00
-- url     : https://prove2.me/theorems/1ac7c8c9-0924-4b05-9066-d47c8595b482
-- title:
--   Exact three-register Schur encoding space
-- statement:
--   Let $n\ge2$ be the number of qubits. A standard tableau with at most two rows is represented by its sequence of upper- and lower-row insertions, with every prefix containing at least as many upper-row as lower-row insertions. If its final lower row has length $m$, its shape is $(n-m,m)$, its multiplicity label is this tableau, and the associated spin-$j$ irrep has $2j+1=n-2m+1$ states. Index these states by $s=0,\ldots,n-2m$, with spin projection $j-s$.
--
--   Allocate the registers in the order $\mathrm{seq},\mathrm{par},\mathrm{stat}$ with sizes
--
--   $$
--   a_n=n-2,\qquad b_n=\left\lceil\log_2(\lfloor n/2\rfloor+1)\right\rceil,\qquad c_n=\left\lceil\log_2(n+1)\right\rceil.
--   $$
--
--   For a fixed shape, encode the tableau in $\mathrm{seq}$ by the row choices for entries $2,\ldots,n-1$; encode $m$ in $\mathrm{par}$ and $s$ in $\mathrm{stat}$, using most significant bit first binary encodings. Every shape has at most $2^{a_n}$ tableau labels. All $m,s$ indices fit in their allocated registers. This encoding is injective on the full set of Schur basis labels, whose cardinality is $2^n$. The allocated total $t_n=a_n+b_n+c_n$ and the ancillary overhead $t_n-n$ satisfy
--
--   $$
--   t_n=n+2\lfloor\log_2 n\rfloor-1,\qquad t_n-n=2\lfloor\log_2 n\rfloor-1.
--   $$
--
--   This specifies the paper's allocation, including unused ghost coordinates. It supports the full multiplicity decomposition without asserting optimality of the ancillary count or that these ancillas are returned to zero.
-- source:
--   A Practical Quantum Algorithm for the Schur Transform, arXiv:1709.07119v6, PDF p. 14, §3.3 Eqs.(24)–(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P10

attribute [local instance] Classical.propDecidable

/-- Kirby--Strauch, arXiv:1709.07119v6, PDF pp.12--14, (24)--(27),
repeated p.20 item 5. For n >= 2 the chosen allocation encodes every Schur
basis label, including all multiplicities, injectively. The independent
register capacities give the exact total and ancillary overhead. These
are allocation equalities, not lower bounds on all Schur implementations.
The n=1 identity transform is outside the three-register allocation. -/
theorem qubit_register_space (n : ℕ) (hn : 2 ≤ n) :
    seqSize n = n - 2 ∧
    parSize n = Nat.clog 2 (n / 2 + 1) ∧
    statSize n = Nat.clog 2 (n + 1) ∧
    (∀ m : ℕ, m ≤ n / 2 →
      Fintype.card (TwoRowTableau n m) ≤ 2 ^ seqSize n) ∧
    (∀ a : QubitSchurLabel n,
      hammingWeight a.val.1 < 2 ^ parSize n ∧
      a.val.2.val < 2 ^ statSize n) ∧
    Function.Injective (@labelEncoding n) ∧
    Fintype.card (QubitSchurLabel n) = 2 ^ n ∧
    totalSize n = n + 2 * Nat.log 2 n - 1 ∧
    ancillaSize n = 2 * Nat.log 2 n - 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P10

end

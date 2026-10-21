-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_intertwining_space_blocks
-- name    : QAlgorithms.Papers.Independent.Support21.P09.intertwining_space_blocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:41:40.713323+00:00
-- url     : https://prove2.me/theorems/0eec79d9-346a-48c9-bf14-e93fa5edd285
-- title:
--   Exact intertwining-space block structure
-- statement:
--   Let $G$ be a finite group and let $\rho_1,\ldots,\rho_k$ be pairwise inequivalent irreducible complex representations, of respective degrees $d_i>0$, in fixed matrix models. Let $n_i,m_i\ge0$ be integer multiplicities, which may vanish. Set $\phi=\bigoplus_i(I_{n_i}\otimes\rho_i)$ and $\psi=\bigoplus_i(I_{m_i}\otimes\rho_i)$. With $\operatorname{Int}(\phi,\psi)=\{M:\phi(g)M=M\psi(g)\text{ for all }g\}$, one has the equality of sets
--
--   $$
--   \operatorname{Int}(\phi,\psi)=\left\{\bigoplus_{i=1}^k(B_i\otimes I_{d_i}):B_i\in\mathbb C^{n_i\times m_i}\right\}.
--   $$
--
--   This identifies every allowable block and excludes all cross-irreducible blocks, rather than merely counting the dimension of the space. Indices are ordered irreducible, multiplicity, then irreducible coordinate.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 6, Theorem 2: exact intertwining-space block structure

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF p.6, Theorem 2: equality of intertwining spaces, including zero multiplicities.
Irreducibility is supplied by the paragraph immediately before the numbered theorem. -/
theorem intertwining_space_blocks
    {G : Type*} [Group G] [Fintype G] {k : ℕ} (deg n m : Fin k → ℕ)
    (rho : (i : Fin k) → Rep G (Fin (deg i)))
    (hirr : ∀ i, Irreducible (rho i))
    (hineq : ∀ i j, i ≠ j → ¬ EquivalentModels (rho i) (rho j)) :
    {M : Matrix (BlockIndex n deg) (BlockIndex m deg) ℂ |
      MatrixIntertwines (irreducibleBlockAction deg n (fun i => rho i))
        (irreducibleBlockAction deg m (fun i => rho i)) M} =
    {M | ∃ B : (i : Fin k) → Matrix (Fin (n i)) (Fin (m i)) ℂ,
      M = scalarBlocks deg n m B} := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end

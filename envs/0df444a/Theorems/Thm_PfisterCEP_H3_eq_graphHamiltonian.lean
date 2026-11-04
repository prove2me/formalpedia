-- Prove2me | Theorems.Thm_PfisterCEP_H3_eq_graphHamiltonian
-- name    : PfisterCEP.H3_eq_graphHamiltonian
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:26:53.479665+00:00
-- url     : https://prove2.me/theorems/b6adb42c-efe3-4106-9e42-522a2ff0e732
-- title:
--   $H_3$ is the graph Hamiltonian of the all-ones adjacency matrix
-- statement:
--   Let $a_k,a_k^\dagger$ satisfy the canonical commutation relations and let $J$ be the $N\times N$ matrix with every entry equal to $1$. Then, for all real $\hbar,\kappa$,
--
--   $$i\hbar\kappa\Big(\sum_{n<p}a_n^\dagger a_p^\dagger+\sum_n\frac{a_n^{\dagger2}}{2}\Big)+\mathrm{H.c.}=\frac{i\hbar\kappa}{2}\sum_{n,p}J_{np}\,a_n^\dagger a_p^\dagger+\mathrm{H.c.}$$
--
--   That is, $H_3=H_J$: the weight $\tfrac12$ on the self-loops of eq. (4) is exactly what puts $1$ on the diagonal of the adjacency matrix, so the graph of $H_3$ is the complete graph with a loop at every vertex (Fig. 3).
--
--   Differences from the source:
--
--   - generalization: $a_j^\dagger$ is the adjoint of $a_j$ → $a^\dagger$ is any family `ad` with $[a_k,a_l^\dagger]=\delta_{kl}$, $[a_k,a_l]=[a_k^\dagger,a_l^\dagger]=0$; reason: the statement uses only the commutation relations; the adjoint pair of a Fock representation is one instance, so the statement specializes to the source's
--   - reading: the adjacency matrix of $H_3$ has all its elements equal to 1 → $H_3=H_J$ as elements of the algebra, with $H_G$ the graph Hamiltonian; reason: 'the adjacency matrix of $H_3$' means the matrix $G$ with $H_3=H_G$
--   - encoding: H.c. → the explicit conjugate terms $-i\hbar\kappa(\sum_{n<p}a_pa_n+\sum_na_n^2/2)$; reason: the conjugate of $i\hbar\kappa\,a_n^\dagger a_p^\dagger$ with real $\hbar\kappa$; same operator
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column, eq. (4)

import Mathlib
import Definitions.Def_PfisterCEP_IsCCR
import Definitions.Def_PfisterCEP_graphHamiltonian
import Definitions.Def_PfisterCEP_H3

namespace PfisterCEP

/-- **`H₃` is the graph Hamiltonian of the all-ones adjacency matrix.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column, eq. (4) and "The adjacency matrix has all its elements equal
to 1".

For modes satisfying the CCR, `H₃ = H_J` with `J` the `N × N` matrix of ones: the weight `1/2` on
the self-loops `a†ₙ²/2` of (4) is what puts `1` on the diagonal.

**Formalization Note** Only the clauses `[aₖ, aₗ] = 0`, `[a†ₖ, a†ₗ] = 0` of the CCR are needed to
symmetrize `∑_{n<p}`; the full `IsCCR` is assumed as in the paper. -/
theorem H3_eq_graphHamiltonian {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) (hccr : IsCCR a ad) (ħ κ : ℝ) : H3 ħ κ a ad = graphHamiltonian ħ κ (Matrix.of fun _ _ => (1 : ℝ)) a ad := by sorry

end PfisterCEP

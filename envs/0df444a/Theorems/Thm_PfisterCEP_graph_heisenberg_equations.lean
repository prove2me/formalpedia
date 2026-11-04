-- Prove2me | Theorems.Thm_PfisterCEP_graph_heisenberg_equations
-- name    : PfisterCEP.graph_heisenberg_equations
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:27:18.864223+00:00
-- url     : https://prove2.me/theorems/aba7e1db-66b8-4f4a-8ae2-fcad13a3f24b
-- title:
--   Heisenberg equations of a graph Hamiltonian: coupling matrix $=\kappa\,G$
-- statement:
--   Let $a_k,a_k^\dagger$ ($k=1,\dots,N$) satisfy the canonical commutation relations, let $\hbar\neq0$ and $\kappa$ be real, and let $G$ be a real symmetric $N\times N$ matrix. For the graph Hamiltonian $H_G=\frac{i\hbar\kappa}{2}\sum_{n,p}G_{np}a_n^\dagger a_p^\dagger+\mathrm{H.c.}$ and every mode $k$,
--
--   $$\frac{i}{\hbar}[H_G,a_k]=\kappa\sum_{p=1}^N G_{kp}\,a_p^\dagger,\qquad \frac{i}{\hbar}[H_G,a_k^\dagger]=\kappa\sum_{p=1}^N G_{kp}\,a_p .$$
--
--   So the Heisenberg equations of the modes form a linear system whose matrix is $\kappa$ times the adjacency matrix of the graph. This is the bridge between the graph picture and the squeezing dynamics: the squeezed quadrature combinations are read off the eigenvectors of $G$.
--
--   Differences from the source:
--
--   - generalization: $a_j^\dagger$ is the adjoint of $a_j$ → $a^\dagger$ is any family `ad` with $[a_k,a_l^\dagger]=\delta_{kl}$, $[a_k,a_l]=[a_k^\dagger,a_l^\dagger]=0$; reason: the statement uses only the commutation relations; the adjoint pair of a Fock representation is one instance, so the statement specializes to the source's
--   - reading: the matrix of the Heisenberg system for the modes is proportional to the adjacency matrix → the explicit equations $\frac{i}{\hbar}[H_G,a_k]=\kappa\sum_pG_{kp}a_p^\dagger$ and $\frac{i}{\hbar}[H_G,a_k^\dagger]=\kappa\sum_pG_{kp}a_p$ for $H_G=\frac{i\hbar\kappa}{2}\sum_{n,p}G_{np}a_n^\dagger a_p^\dagger+\mathrm{H.c.}$; reason: the page states proportionality in words; $H_G$ is the common form of eqs. (1), (3), (4), and the proportionality constant is $\kappa$
--   - generalization: the graphs of Figs. 1–3 (complete graphs with or without loops) → every real symmetric matrix $G$; reason: the claim is stated for 'the graph so defined' generally; Figs. 1–3 are special cases
--   - encoding: $\hbar$, the reduced Planck constant ($\hbar>0$) → any real $\hbar\neq0$; reason: the Heisenberg equation divides by $\hbar$; $\hbar>0$ is a special case and $\hbar=0$ is excluded only because the generator is undefined there
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column

import Mathlib
import Definitions.Def_PfisterCEP_IsCCR
import Definitions.Def_PfisterCEP_graphHamiltonian
import Definitions.Def_PfisterCEP_heisenbergGen

namespace PfisterCEP

/-- **Heisenberg equations of a graph Hamiltonian: the coupling matrix is `κ` times the adjacency
matrix.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column: "It is straightforward to see from the Heisenberg equations for
the modes {an}1...N that the matrix describing this system of coupled differential equations is
proportional to the adjacency matrix [1] of the graph so defined."

For a symmetric real matrix `G` and modes satisfying the CCR,

  `(i/ħ)[H_G, aₖ] = κ ∑ₚ G_{kp} a†ₚ`,   `(i/ħ)[H_G, a†ₖ] = κ ∑ₚ G_{kp} aₚ`.

**Formalization Note** `G` symmetric (the adjacency matrix of an undirected graph with loops);
`ħ ≠ 0`; `κ` any real. -/
theorem graph_heisenberg_equations {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) (hccr : IsCCR a ad) (ħ κ : ℝ) (hħ : ħ ≠ 0) (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsSymm) (k : Fin N) : heisenbergGen ħ (graphHamiltonian ħ κ G a ad) (a k) = (κ : ℂ) • ∑ p, (G k p : ℂ) • ad p ∧ heisenbergGen ħ (graphHamiltonian ħ κ G a ad) (ad k) = (κ : ℂ) • ∑ p, (G k p : ℂ) • a p := by sorry

end PfisterCEP

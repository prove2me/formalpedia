-- Prove2me | Theorems.Thm_SteerableE2CNN_irrep_decomposition_kernel_constraint
-- name    : SteerableE2CNN.irrep_decomposition_kernel_constraint
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:38:17.12928+00:00
-- url     : https://prove2.me/theorems/2435e2d8-ad0a-40f2-a67b-d46e6dc15c53
-- title:
--   Section 2.4, eqs. (3)-(4): the kernel constraint decomposes into irrep constraints
-- statement:
--   Let $G\le\mathrm{O}(2)$. Let $\{\psi_i\}_{i\in I_{\mathrm{out}}}$ and $\{\psi_j\}_{j\in I_{\mathrm{in}}}$ be finite families of irreducible representations of $G$, of dimensions $d_i$ and $d_j$. Let $\rho_{\mathrm{out}}$ and $\rho_{\mathrm{in}}$ be representations of $G$ with changes of basis $Q_{\mathrm{out}}$, $Q_{\mathrm{in}}$ such that
--
--   $$\rho_{\mathrm{out}}=Q_{\mathrm{out}}^{-1}\Big[\bigoplus_{i\in I_{\mathrm{out}}}\psi_i\Big]Q_{\mathrm{out}},\qquad \rho_{\mathrm{in}}=Q_{\mathrm{in}}^{-1}\Big[\bigoplus_{j\in I_{\mathrm{in}}}\psi_j\Big]Q_{\mathrm{in}}.$$
--
--   1. A kernel $k$ satisfies the constraint (2) for $(\rho_{\mathrm{in}},\rho_{\mathrm{out}})$ if and only if every block $\kappa^{ij}$ of $\kappa=Q_{\mathrm{out}}kQ_{\mathrm{in}}^{-1}$ satisfies the irrep constraint
--
--   $$\kappa^{ij}(gx)=\psi_i(g)\,\kappa^{ij}(x)\,\psi_j(g)^{-1}\qquad\forall g\in G,\ x\in\mathbb{R}^2.\tag{3}$$
--
--   2. Conversely, if $\kappa^{ij}$ is a solution of (3) for every pair $(i,j)$, then $k=Q_{\mathrm{out}}^{-1}\kappa\,Q_{\mathrm{in}}$ is a solution of (2), where $\kappa$ is the matrix with blocks $\kappa^{ij}$. This kernel is $\sum_{ij}Q_{\mathrm{out}}^{-1}\overline{\kappa}^{ij}Q_{\mathrm{in}}$, with $\overline{\kappa}^{ij}$ the zero-padded blocks (eq. 4).
--
--   So bases of the block solution spaces give a basis of the $G$-steerable kernels as in eq. (4).
--
--   **Formalization Note** The changes of basis are matrices between $\mathbb{R}^m$ and $\bigoplus_i\mathbb{R}^{d_i}$, given together with their two-sided inverses. The basis statement of eq. (4) appears as the two directions of the correspondence $k\leftrightarrow(\kappa^{ij})$.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.4, eqs. (2), (3), (4), p. 4; Appendix E, eq. (12), p. 25

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem irrep_decomposition_kernel_constraint (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {Iout Iin : Type*} [Fintype Iout] [DecidableEq Iout] [Fintype Iin] [DecidableEq Iin]
    {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (ψout : ∀ i, MatRep G (Fin (dOut i))) (ψin : ∀ j, MatRep G (Fin (dIn j)))
    (hψout : ∀ i, IsIrrep (ψout i)) (hψin : ∀ j, IsIrrep (ψin j))
    (ρout : MatRep G m) (ρin : MatRep G n)
    (Qout : Matrix (Σ i, Fin (dOut i)) m ℝ) (Qout' : Matrix m (Σ i, Fin (dOut i)) ℝ)
    (hQout : Qout' * Qout = 1) (hQout' : Qout * Qout' = 1)
    (Qin : Matrix (Σ j, Fin (dIn j)) n ℝ) (Qin' : Matrix n (Σ j, Fin (dIn j)) ℝ)
    (hQin : Qin' * Qin = 1) (hQin' : Qin * Qin' = 1)
    (hρout : ∀ g, repMat ρout g = Qout' * Matrix.blockDiagonal' (fun i => repMat (ψout i) g) * Qout)
    (hρin : ∀ g, repMat ρin g = Qin' * Matrix.blockDiagonal' (fun j => repMat (ψin j) g) * Qin) :
    (∀ k : Plane → Matrix m n ℝ, IsSteerable G ρin ρout k ↔
      ∀ i j, IsSteerable G (ψin j) (ψout i) (fun x => kernelBlock (Qout * k x * Qin') i j)) ∧
    (∀ κ : ∀ i j, Plane → Matrix (Fin (dOut i)) (Fin (dIn j)) ℝ,
      (∀ i j, IsSteerable G (ψin j) (ψout i) (κ i j)) →
      IsSteerable G ρin ρout
        (fun x => Qout' *
          (Matrix.of (fun (p : Σ i, Fin (dOut i)) (q : Σ j, Fin (dIn j)) => κ p.1 q.1 x p.2 q.2) :
            Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) * Qin)) := by sorry

end SteerableE2CNN

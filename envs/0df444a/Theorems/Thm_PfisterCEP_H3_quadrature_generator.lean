-- Prove2me | Theorems.Thm_PfisterCEP_H3_quadrature_generator
-- name    : PfisterCEP.H3_quadrature_generator
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:27:50.305052+00:00
-- url     : https://prove2.me/theorems/35aaf868-21d4-4878-a8c2-7ae1dc2b0b15
-- title:
--   Heisenberg system of $H_3$ in quadratures: $\dot{\mathbf P}=-N\kappa\mathbf P$, $\dot X=N\kappa X$, differences conserved
-- statement:
--   Let $a_k,a_k^\dagger$ satisfy the canonical commutation relations, $\hbar\neq0$, $\kappa$ real, and write $D(x)=\frac{i}{\hbar}[H_3,x]$ for the Heisenberg generator of $H_3$. Then
--
--   1. $D(\mathbf P)=-N\kappa\,\mathbf P$ for the phase sum $\mathbf P=\sum_jP_j$;
--   2. $D(X)=N\kappa\,X$ for the total amplitude $X=\sum_jX_j$;
--   3. $D(X_k-X_l)=0$ for all amplitude differences;
--   4. $D(P_k-P_l)=0$ for all phase differences.
--
--   These are the Heisenberg equations of $H_3$ in quadrature form: $\mathbf P$ is an eigenvector of the generator with eigenvalue $-N\kappa$ (squeezing at rate $N\kappa$ when $\kappa>0$), and the differences have eigenvalue $0$ (constants of the motion).
--
--   Differences from the source:
--
--   - generalization: $a_j^\dagger$ is the adjoint of $a_j$ → $a^\dagger$ is any family `ad` with $[a_k,a_l^\dagger]=\delta_{kl}$, $[a_k,a_l]=[a_k^\dagger,a_l^\dagger]=0$; reason: the statement uses only the commutation relations; the adjoint pair of a Fock representation is one instance, so the statement specializes to the source's
--   - reading: $\mathbf P(t)=\mathbf P(0)e^{-N\kappa t}$; the amplitude differences are constants of the motion (zero eigenvalue) → the generator identities $D(\mathbf P)=-N\kappa\mathbf P$ and $D(X_k-X_l)=0$; reason: these are the eigen-equations of the Heisenberg system from which the page's solutions follow; the solutions themselves are clauses of the goal
--   - generalization: not printed → $D(X)=N\kappa X$ and $D(P_k-P_l)=0$; reason: the total-amplitude companion (Fig. 3) and the phase differences complete the quadrature picture; they are needed for the 'only squeezed operator' clause of the goal
--   - generalization: $\kappa$ the nonlinear coupling constant (sign not fixed) → every real $\kappa$; reason: the identities are algebraic and hold for every $\kappa$
--   - encoding: $\hbar$, the reduced Planck constant ($\hbar>0$) → any real $\hbar\neq0$; reason: the Heisenberg equation divides by $\hbar$; $\hbar>0$ is a special case and $\hbar=0$ is excluded only because the generator is undefined there
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column; Sec. c, p.2 ("the Heisenberg system for H3")

import Mathlib
import Definitions.Def_PfisterCEP_IsCCR
import Definitions.Def_PfisterCEP_ampQuad
import Definitions.Def_PfisterCEP_phaseQuad
import Definitions.Def_PfisterCEP_ampSum
import Definitions.Def_PfisterCEP_phaseSum
import Definitions.Def_PfisterCEP_H3
import Definitions.Def_PfisterCEP_heisenbergGen

namespace PfisterCEP

/-- **Heisenberg system of `H₃` in quadrature form.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column ("The only squeezed operator here is the phase sum
P(t) = P(0)e^{−Nκt} … the amplitude differences, are now constants of the motion (zero
eigenvalue)") and Sec. c, p.2 ("the Heisenberg system for H3").

With `D x = (i/ħ)[H₃, x]` and modes satisfying the CCR:
1. `D 𝐏 = −Nκ 𝐏` (phase sum);
2. `D X = Nκ X` (total amplitude);
3. `D (Xₖ − Xₗ) = 0` (amplitude differences);
4. `D (Pₖ − Pₗ) = 0` (phase differences).

**Formalization Note** `ħ ≠ 0`, `κ` any real. Clause 4 is not printed; it is the companion of
clause 3 for the phase quadratures and is needed for the "only squeezed operator" clause of the
goal. -/
theorem H3_quadrature_generator {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) (hccr : IsCCR a ad) (ħ κ : ℝ) (hħ : ħ ≠ 0) : heisenbergGen ħ (H3 ħ κ a ad) (phaseSum a ad) = ((-(N * κ) : ℝ) : ℂ) • phaseSum a ad ∧ heisenbergGen ħ (H3 ħ κ a ad) (ampSum a ad) = ((N * κ : ℝ) : ℂ) • ampSum a ad ∧ (∀ k l : Fin N, heisenbergGen ħ (H3 ħ κ a ad) (ampQuad a ad k - ampQuad a ad l) = 0) ∧ (∀ k l : Fin N, heisenbergGen ħ (H3 ħ κ a ad) (phaseQuad a ad k - phaseQuad a ad l) = 0) := by sorry

end PfisterCEP

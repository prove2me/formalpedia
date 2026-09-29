-- Prove2me | Theorems.Thm_SX_eq_zero_of_expSum_vanishes
-- name    : SX.eq_zero_of_expSum_vanishes
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T11:11:59.137772+00:00
-- url     : https://prove2.me/theorems/fd939533-ac90-4615-9614-02acc8274f65
-- title:
--   Zero estimate: vanishing on the whole lattice kills the coefficients
-- statement:
--   **The zero estimate.** An exponential polynomial that vanishes at *every* lattice point has all coefficients zero.
--
--   Precisely: with $x$ and $y$ both $\mathbb{Q}$-linearly independent and $l \ge 2$, if
--   $$\sum_{\lambda} p_\lambda\, e^{\langle\lambda,x\rangle\,\langle m,y\rangle} = 0 \qquad \text{for every } m \in \mathbb{N}^l,$$
--   then every $p_\lambda$ with $\lambda$ in the box vanishes.
--
--   This is a Vandermonde argument rather than an analytic one, and it is what closes the induction: the descent step forces vanishing everywhere, and this says that forces the coefficients to be zero, contradicting the non-zero coefficient Siegel produced.
--
--   Two independence facts do the work. $\mathbb{Q}$-linear independence of $x$ makes the exponents $\langle\lambda,x\rangle$ pairwise distinct across the box. $\mathbb{Q}$-linear independence of $y$, with $l \ge 2$, makes $\lambda \mapsto \bigl(e^{\langle\lambda,x\rangle y_j}\bigr)_j$ injective: if some $\omega \ne 0$ had $\omega y_j \in 2\pi i\,\mathbb{Z}$ for every $j$, then two of the $y_j$ would have rational ratio.
--
--   **$l \ge 2$ is necessary, not cosmetic.** For $l = 1$ the statement is false — vanishing along a single arithmetic progression only forces the coefficients to cancel in blocks.
--
--   **Where it anchors.** `linearIndependent_monoidHom` (Dedekind's theorem on independence of characters) and `Complex.exp_eq_one_iff`.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley 1966, Ch. 2; K. Ramachandra, Contributions to the theory of transcendental numbers I, Acta Arith. 14 (1968) 65-72; M. Waldschmidt, Auxiliary functions in transcendence proofs, arXiv:0908.4024, sections 3.1.3 and 3.4 (Theorem 3.9); M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Springer 2000, Theorem 1.12.

import Definitions.Def_SX

open Complex

namespace SX

theorem eq_zero_of_expSum_vanishes
    {d l : ℕ} (hl : 2 ≤ l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (L : ℕ) (p : (Fin d → ℕ) → ℤ)
    (h : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0) :
    ∀ lam ∈ SX.box d L, p lam = 0 := by
  sorry

end SX

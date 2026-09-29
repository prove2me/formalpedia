-- Prove2me | Theorems.Thm_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
-- name    : Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/910c263b-f3d8-509d-9115-213ee11e5d98
-- title:
--   Descent of a function through a rational map, up to Frobenius
-- statement:
--   Let $F$ be a field and let $k$ be an algebraically closed field equipped with an $F$-algebra structure. Let $f_n, f_d, g_n, g_d \in F[X]$, and assume that $f_n$ is not a constant $F$-multiple of $f_d$, i.e. $f_n \neq c\,f_d$ for every $c \in F$ (so that the rational function $f_n/f_d$ is non-constant). Let $m : k \to k$ be an arbitrary function of sets, with no algebraicity or continuity assumed, and let $S \subseteq k$ be a finite set such that for every $x \in k$ with $x \notin S$ one has $f_d(x) \neq 0$, $g_d(x) \neq 0$ and $m\bigl(f_n(x)/f_d(x)\bigr) = g_n(x)/g_d(x)$, where the polynomials are evaluated at $x$ through the structure map $F \to k$. The conclusion is that there exist a natural number $t$, polynomials $h_n, h_d \in F[X]$ and a finite set $T \subseteq k$ such that for every $u \in k$ with $u \notin T$ one has $h_d(u) \neq 0$ and $m(u)^{q^t} = h_n(u)/h_d(u)$, where $q = \mathrm{ringExpChar}\,F$ is the characteristic exponent of $F$ (so $q = 1$ in characteristic zero, and $q = p$ in characteristic $p$). Thus $m$ agrees, off a finite set, with an $F$-rational function after raising to a power of the Frobenius.
--
--   This is the one-variable field-theoretic core of descent of a map through a possibly inseparable dominant rational map: a function which becomes $F$-rational after precomposition with a non-constant $F$-rational function is itself $F$-rational up to a power of Frobenius, the Frobenius power being genuinely necessary in characteristic $p$. It is used in the treatment of rational homomorphisms of Weierstrass curves, in [`WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet`](thm.html#WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet) and [`WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k]
    (fn fd gn gd : Polynomial F) (hf : ∀ c : F, fn ≠ Polynomial.C c * fd)
    (m : k → k) (S : Set k) (hS : S.Finite)
    (H : ∀ x : k, x ∉ S → Polynomial.aeval x fd ≠ 0 ∧ Polynomial.aeval x gd ≠ 0 ∧
      m (Polynomial.aeval x fn / Polynomial.aeval x fd) =
        Polynomial.aeval x gn / Polynomial.aeval x gd) :
    ∃ (t : ℕ) (hn hd : Polynomial F) (T : Set k), T.Finite ∧ ∀ u : k, u ∉ T →
      Polynomial.aeval u hd ≠ 0 ∧
        m u ^ ringExpChar F ^ t = Polynomial.aeval u hn / Polynomial.aeval u hd := by sorry

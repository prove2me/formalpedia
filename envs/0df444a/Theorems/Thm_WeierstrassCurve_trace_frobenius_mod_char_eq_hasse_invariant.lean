-- Prove2me | Theorems.Thm_WeierstrassCurve_trace_frobenius_mod_char_eq_hasse_invariant
-- name    : WeierstrassCurve.trace_frobenius_mod_char_eq_hasse_invariant
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:19:31.756357+00:00
-- url     : https://prove2.me/theorems/a25e65c1-bc98-4637-b758-1bee8a67811b
-- title:
--   Trace of Frobenius modulo $p$ equals the Hasse invariant: over $\mathbb F_{p^m}$ ($p$ odd), $a_E \equiv A_p(E)^{1 + p + \dots + p^{m-1}} \pmod p$, so $p \mid a_E$ if and only if $A_p(E) = 0$
-- statement:
--   Let $p$ be an odd prime, let $F$ be a finite field of characteristic $p$ with $q = p^m$ elements, and let $E$ be an elliptic curve over $F$ given by a Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. Put $a_E = q + 1 - \#E(F)$ (the trace of Frobenius; $\#E(F)$ counts the point at infinity) and
--
--   $$\Psi_2^2(X) = 4X^3 + b_2X^2 + 2b_4X + b_6,$$
--
--   so that $(2y + a_1x + a_3)^2 = \Psi_2^2(x)$ on $E$. Let $A_p(E) = [X^{p-1}]\,\Psi_2^2(X)^{(p-1)/2} \in F$ be the Hasse invariant. Then, as elements of $F$ (that is, modulo $p$, since $\mathbb Z \to F$ factors through $\mathbb F_p$):
--
--   1. $a_E = [X^{q-1}]\,\Psi_2^2(X)^{(q-1)/2}$;
--   2. $a_E = A_p(E)^{1 + p + \dots + p^{m-1}}$;
--   3. $p \mid a_E$ if and only if $A_p(E) = 0$.
--
--   Part 3 is the Hasse invariant criterion: $E$ is supersingular ($p \mid a_E$) exactly when its Hasse invariant vanishes. For a short equation $y^2 = f(x)$ one has $\Psi_2^2 = 4f$ and $4^{(p-1)/2} = 1$ in $F$, so $A_p(E)$ is the classical coefficient of $x^{p-1}$ in $f(x)^{(p-1)/2}$. Examples over $\mathbb F_5$: for $y^2 = x^3 + 1$, $f^2 = x^6 + 2x^3 + 1$ has no $x^4$ term, so $A_5 = 0$, and indeed $\#E(\mathbb F_5) = 6$, $a_E = 0$; for $y^2 = x^3 + x$, the $x^4$ coefficient of $f^2$ is $2$, and $\#E(\mathbb F_5) = 4$, $a_E = 2$.
--
--   Proof idea: completing the square, the number of $y \in F$ over a given $x$ is $1 + \chi(\Psi_2^2(x))$ with $\chi$ the quadratic character, so $a_E = -\sum_{x \in F} \chi(\Psi_2^2(x))$. In $F$, $\chi(u) = u^{(q-1)/2}$, and $\sum_{x \in F} x^k$ equals $-1$ for $k = q - 1$ and $0$ for every other $0 \le k < 2(q-1)$; as $\deg \Psi_2^{2\,(q-1)/2} < 2(q-1)$, this gives 1. Writing $(p^{m+1}-1)/2 = (p-1)/2 + p\,(p^m-1)/2$ and using $g(X)^p = g^{(p)}(X^p)$ in characteristic $p$ gives Manin's recursion $H_{m+1} = A_p(E)\,H_m^{\,p}$ for $H_m = [X^{p^m-1}]\,\Psi_2^2(X)^{(p^m-1)/2}$, hence 2 by induction ($H_0 = 1$). Part 3 follows from 2, since $p \mid a_E$ means $a_E = 0$ in $F$, $F$ has no zero divisors, and the exponent is positive.
--
--   **Formalization Note**: $F$ is a field with `[Fintype F]` and `[CharP F p]`, `hq : Fintype.card F = p ^ m`, `hp : p ≠ 2`; $E$ is `W : WeierstrassCurve F` with `[W.IsElliptic]`. $\#E(F)$ is `Nat.card W.toAffine.Point` (Mathlib's type of nonsingular affine points together with the point at infinity), so $a_E$ is the integer `(Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point`, and congruences modulo $p$ are stated through its cast to `F`. $\Psi_2^2$ is Mathlib's division polynomial `W.Ψ₂Sq`, the exponent $1 + p + \dots + p^{m-1}$ is `∑ i ∈ Finset.range m, p ^ i`, and coefficients are `Polynomial.coeff`. The three parts are the three conjuncts.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Theorem V.4.1 and its proof; Yu. I. Manin, The Hasse-Witt matrix of an algebraic curve, Izv. Akad. Nauk SSSR Ser. Mat. 25 (1961), 153-172

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.trace_frobenius_mod_char_eq_hasse_invariant
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    {m : ℕ} (hq : Fintype.card F = p ^ m) (W : WeierstrassCurve F) [W.IsElliptic] :
    ((((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
        (W.Ψ₂Sq ^ ((Fintype.card F - 1) / 2)).coeff (Fintype.card F - 1)) ∧
    ((((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
        (W.Ψ₂Sq ^ ((p - 1) / 2)).coeff (p - 1) ^ (∑ i ∈ Finset.range m, p ^ i)) ∧
    ((p : ℤ) ∣ (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) ↔
        (W.Ψ₂Sq ^ ((p - 1) / 2)).coeff (p - 1) = 0) := by
  sorry

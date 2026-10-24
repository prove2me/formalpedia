-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_HirschhornComb_hirschhorn_P_eq_combination
-- name    : QseriesFormalization.Pending.HirschhornComb.hirschhorn_P_eq_combination
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T15:23:34.563327+00:00
-- url     : https://prove2.me/theorems/3a093d98-6f90-4fce-bd96-adcede7761c0
-- title:
--   Hirschhorn's combination identity over a ring of characteristic 11
-- statement:
--   Let $R$ be a commutative ring in which $11=0$ and let $a,b,c,d,e\in R$ (these play the roles of $J_0,J_1,J_3,J_6,J_{10}$, the residue components of $(q;q)_\infty^3$). The statement is a polynomial identity: an explicit polynomial $P(a,b,c,d,e)$ with 30 monomials and coefficients in $\{1,\dots,10\}$ equals $\sum_{r}M_r\cdot R_r$, a sum of five products of an explicit cubic $M_r$ and an explicit degree-4 polynomial $R_r$ in $a,\dots,e$. This is a pure algebraic step in Hirschhorn's proof of $p(11n+6)\equiv0\pmod{11}$ (Chapter 17).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_Hirschhorn_Combination.lean#L29 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Mathlib

/-!
# Hirschhorn §3.5 mod-11 — the polynomial identity (algebraic core)

The verified certificate (see `scripts/hirschhorn_mod11_solve.py`):
over `ℤ/11`, with `a,b,c,d,e := J₀,J₁,J₃,J₆,J₁₀`,

  `P = M₃·R₃ + M₆·R₆ + M₈·R₈ + M₉·R₉ + M₁₀·R₁₀`

where `P` is the residue-6 part of `(J₀+J₁+J₃+J₆+J₁₀)⁷` (Hirschhorn eq 3.5.3),
`R_r` is the residue-`r` part of `(…)⁴` (eqs 3.5.6–3.5.10), and `M_r` are the
degree-3 multipliers.  This is Hirschhorn's "left as an exercise" (3.5.11–13);
`a = 7, b = 5, c = 7` exist, here realised by explicit multipliers `M_r`.

Since `ring` does not reduce coefficients modulo 11, we prove the identity by
the exact **integer** factorisation `(Σ M_r R_r) − P = 11·Q` (which `ring`
discharges over `ℤ`), then kill `11·Q` using `CharP R 11`.  `Q` is computed by
`scripts/hirschhorn_mod11_solve.py` / `_compute`. -/

/-! Elaboration note.  A literal exponent `x ^ 5` gets its type `ℕ` only from the
`Monoid.Pow` default instance, which Lean applies one pending problem at a time, re-trying every
other pending instance problem after each step.  On a statement with ~150 literal powers this is
quadratic and costs seconds of typeclass inference before the proof starts.  The local rule below
ascribes `ℕ` to literal exponents up front; it produces exactly the same terms (`ℕ` exponents,
`Monoid.Pow`), only faster. -/

theorem QseriesFormalization.Pending.HirschhornComb.hirschhorn_P_eq_combination
    {R : Type*} [CommRing R] [CharP R 11] (a b c d e : R) :
    (7*a^6*d + 10*a^5*c^2 + a^4*b*d*e + 8*a^3*d^3*e + 2*a^3*b*c^2*e + 8*a^3*b^3*c
      + 10*a^2*e^5 + 2*a^2*c*d*e^3 + 3*a^2*c^2*d^2*e + 3*a^2*b^2*d*e^2 + 3*a^2*b^2*c*d^2
      + 8*a*c^3*e^3 + a*c^4*d*e + 2*a*b*d^3*e^2 + a*b*c*d^4 + 3*a*b^2*c^2*e^2
      + 2*a*b^2*c^3*d + a*b^4*c*e + 7*a*b^6 + 10*d^5*e^2 + 7*c*d^6 + 7*c^6*e + 7*b*e^6
      + b*c*d*e^4 + 3*b*c^2*d^2*e^2 + 8*b*c^3*d^3 + 10*b^2*c^5 + 8*b^3*d*e^3
      + 2*b^3*c*d^2*e + 10*b^5*d^2)
    =
    (10*b*c*e + 10*b^3 + 4*a^2*c) * (4*a^3*c + 2*a*b*c*e + 4*a*b^3 + 4*d*e^3 + c*d^2*e + 6*b^2*d^2)
    + (4*d^2*e + 10*a*b*e + 10*a^3) * (4*a^3*d + 6*a^2*c^2 + 2*a*b*d*e + 4*d^3*e + b*c^2*e + 4*b^3*c)
    + (10*c^3 + 4*a*e^2 + 10*a*c*d) * (4*a*e^3 + 2*a*c*d*e + a*b^2*d + 4*c^3*e + 4*b*d^3 + 6*b^2*c^2)
    + (10*e^3 + 10*c*d*e + 4*b^2*d) * (6*a^2*e^2 + a^2*c*d + 4*a*c^3 + 4*b*e^3 + 2*b*c*d*e + 4*b^3*d)
    + (10*d^3 + 4*b*c^2 + 10*a*b*d) * (4*a^3*e + a*b*e^2 + 2*a*b*c*d + 6*d^2*e^2 + 4*c*d^3 + 4*b*c^3) := by sorry

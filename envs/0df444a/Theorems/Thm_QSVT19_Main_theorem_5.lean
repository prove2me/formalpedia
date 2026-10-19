-- Prove2me | Theorems.Thm_QSVT19_Main_theorem_5
-- name    : QSVT19.Main.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:29.247581+00:00
-- url     : https://prove2.me/theorems/18e641a9-02b9-418f-8393-b2191f47b630
-- title:
--   Theorem 5: real parts of quantum signal processing polynomials
-- statement:
--   Let $k\in\mathbb N$ and $\tilde P,\tilde Q\in\mathbb R[x]$. There exist $P,Q\in\mathbb C[x]$ forming a QSP pair of degree $k$ (properties (i)–(iii) of Theorem 3: $\deg P\le k$, $\deg Q\le k-1$, parities $k$ and $k-1\bmod 2$, and $|P(x)|^2+(1-x^2)|Q(x)|^2=1$ on $[-1,1]$) with $\Re[P]=\tilde P$ and $\Re[Q]=\tilde Q$ if and only if
--   1. $\deg\tilde P\le k$ and $\deg\tilde Q\le k-1$;
--   2. $\tilde P$ has parity $k\bmod2$ and $\tilde Q$ has parity $k-1\bmod 2$;
--   3. for all $x\in[-1,1]$,
--   $$\tilde P(x)^2+(1-x^2)\tilde Q(x)^2\le 1.$$
--
--   This tells which real polynomials can be realized as real parts of QSP polynomials; it underlies Corollary 10 and hence Corollary 18.
--
--   **Formalization Note** $\Re[P]$ is the polynomial of the real parts of the coefficients. The theorem's parenthetical remark on imaginary parts is not included.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 11, Theorem 5

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 5, p. 11: "Let k ∈ N be fixed. Let P̃, Q̃ ∈ R[x], there exists some
P, Q ∈ C[x] satisfying properties (i)-(iii) of Theorem 3 such that P̃ = ℜ[P], Q̃ = ℜ[Q], if and
only if P̃, Q̃ satisfy properties (i)-(ii) of Theorem 3 and
(vi) ∀x ∈ [−1, 1]: P̃(x)^2 + (1 − x^2)Q̃^2 ≤ 1."

**Formalization Note.** Properties (i)–(iii) of Theorem 3 (p. 8) are `IsQSPPair k P Q`;
`ℜ[P] = P̃` is `RePartEq P Pt` (real parts of the coefficients, §2). Properties (i)–(ii) for the
real pair are written out: `deg P̃ ≤ k`, `deg Q̃ ≤ k − 1` (as `Q̃.degree < k`), `P̃` of parity
`k mod 2`, `Q̃` of parity `k − 1 mod 2` (as `HasParity _ (k + 1)` of the complexification). The
printed "`Q̃^2`" in (vi) is `Q̃(x)^2`. The parenthetical remark after the theorem (ℑ variants,
`Q̃ ≡ 0`) is not part of this statement. -/
theorem theorem_5 (k : ℕ) (Pt Qt : ℝ[X]) :
    (∃ P Q : ℂ[X], IsQSPPair k P Q ∧ RePartEq P Pt ∧ RePartEq Q Qt) ↔ ((Pt.degree ≤ k ∧ Qt.degree < k) ∧ (QAlgorithms.HasParity (Pt.map Complex.ofRealHom) k ∧ QAlgorithms.HasParity (Qt.map Complex.ofRealHom) (k + 1)) ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) := by sorry

end QSVT19.Main

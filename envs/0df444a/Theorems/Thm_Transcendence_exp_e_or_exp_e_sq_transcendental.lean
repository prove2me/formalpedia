-- Prove2me | Theorems.Thm_Transcendence_exp_e_or_exp_e_sq_transcendental
-- name    : Transcendence.exp_e_or_exp_e_sq_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:39:36.435189+00:00
-- url     : https://prove2.me/theorems/88f16d63-3fc8-487c-a4fe-f9b72badba3e
-- title:
--   Schneider's eighth problem: at least one of e^e and e^{e²} is transcendental
-- statement:
--   At least one of the two numbers
--
--   $$e^{e} \qquad\text{and}\qquad e^{e^{2}}$$
--
--   is transcendental.
--
--   This is the last of the eight open problems in Schneider's book (1957), as quoted by Waldschmidt (1973), p. 191.
--
--   **Proof.** Apply `DiazModulus.two_algebraically_independent_of_exp_column` at $x = y = (1, e)$. Both pairs are linearly independent over $\mathbb{Q}$ because $e$ is irrational. The column $y_2 = e$ carries exactly $e^{e}$ and $e^{e^{2}}$. If both were algebraic, all eight numbers would be algebraic over $\mathbb{Q}(e)$, a field of transcendence degree one, against the theorem.
--
--   **Novelty.** None: this is the case $r = 1$ of the *Solution du problème de Schneider* in Waldschmidt (1973), p. 192, which the paper deduces from its Corollaire 1 (for rational $r$, one of $e^{e^r}$, $e^{e^{2r}}$ is transcendental). The substitution used here is Corollaire 1's, with $x_1$ and $x_2$ exchanged. By the note added in proof (p. 202), Brownawell solved the problem independently. The contribution of this node is the formal proof.
-- source:
--   The problem: T. Schneider, Einführung in die transzendenten Zahlen, Springer, Berlin, 1957, as quoted in M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, p. 191. The solution: the same paper, p. 192 (Solution du problème de Schneider, r = 1, deduced from Corollaire 1); found independently by W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- One of `e^e` and `e^{e²}` is transcendental.

This is the problem in the title of M. Waldschmidt, *Solution du huitième problème de Schneider*,
J. Number Theory 5 (1973), 191–202. It is the Théorème there
(`DiazModulus.two_algebraically_independent_of_exp_column`) at `x = y = (1, e)`: the column is
`e^e`, `e^{e²}`, and if both were algebraic, the eight numbers `1, e, 1, e, e, e^e, e^e, e^{e²}`
would all be algebraic over `ℚ(e)`, so no two of them could be algebraically independent. -/
theorem exp_e_or_exp_e_sq_transcendental :
    Transcendental ℚ (Complex.exp (Complex.exp 1)) ∨
      Transcendental ℚ (Complex.exp (Complex.exp 1 ^ 2)) := by
  sorry

end Transcendence

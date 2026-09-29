-- Prove2me | Theorems.Thm_PvsNP_isPolyTime_comp
-- name    : PvsNP.isPolyTime_comp
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T06:30:17.689152+00:00
-- url     : https://prove2.me/theorems/2dd0b515-490e-4f4c-87e7-729dfcc56968
-- title:
--   Polynomial-time computable functions are closed under composition
-- statement:
--   Let $\alpha$, $\beta$, $\gamma$ be types equipped with canonical bitstring encodings, and let $f : \alpha \to \beta$ and $g : \beta \to \gamma$ be computable in polynomial time by two-stack Turing machines with respect to those encodings. Then the composite $g \circ f$ is computable in polynomial time as well.
--
--   The intended construction is the standard one: run the machine for $f$ on the input, copy its output stack to the input stack of the machine for $g$, and run the machine for $g$. The composed machine can be realised as a single two-stack machine with one stack for each stack of the two component machines. For the time bound, note that a machine writes at most one symbol per step, so on input $x$ the intermediate string $\mathrm{enc}(f(x))$ has length at most $t_f(|\mathrm{enc}(x)|)$, where $t_f$ is the polynomial time bound of the first machine; the total running time is therefore bounded by
--
--   $$t_f(|\mathrm{enc}(x)|) \;+\; O\bigl(t_f(|\mathrm{enc}(x)|)\bigr) \;+\; t_g\bigl(t_f(|\mathrm{enc}(x)|)\bigr),$$
--
--   which is again a polynomial in $|\mathrm{enc}(x)|$ since polynomials with natural-number coefficients are closed under composition, sums and products.
--
--   This closure property is the basic workhorse of polynomial-time complexity theory: it underlies the fact that $\mathsf{P}$ is closed downwards under polynomial-time many-one (Karp) reductions, and hence every completeness argument.
-- source:
--   Stated as `proof_wanted Turing.TM2ComputableInPolyTime.comp` in Mathlib, Mathlib/Computability/TuringMachine/Computable.lean (revision 0df444a360eaa60ab8c11dca51a86af692955474), end of file; mathematical content: Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 1 (Claim 1.6, composition/simulation of Turing machines) and Chapter 2, Definition 2.7 ff.

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem isPolyTime_comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : β → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by sorry

end PvsNP

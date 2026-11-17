-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_E_1
-- name    : ResultantVNP.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:01:06.4662+00:00
-- url     : https://prove2.me/theorems/d13e67b4-a10f-4ad0-9a5f-4c102524b6f3
-- title:
--   Theorem E.1 — univariate resultant signs of constant-free circuits are $\oplus$P-hard
-- statement:
--   For univariate integer polynomials given by constant-free arithmetic circuits, the **negative** and the **positive resultant-sign problems** (is $\mathrm{Res}_x(p,g)<0$, resp. $>0$?) are $\oplus\mathsf P$-hard under deterministic polynomial-time many-one reductions, even with the promise that the resultant is nonzero and both polynomials have positive degree.
--
--   More precisely, from a Boolean circuit $C$ with $m\ge1$ inputs and $s\ge1$ gates one can construct, in time polynomial in $m+s$, constant-free circuits for $p_m,\Phi_C\in\mathbb Z[x]$ such that
--
--   1. $p_m=T_{2^m}$ (the Chebyshev polynomial) and $\mathrm{size}(p_m)=O(m)$;
--   2. $\mathrm{Res}_x(p_m,\Phi_C)\ne0$ and $\mathrm{size}(\Phi_C)=O(m(m+s)+s)$;
--   3. $$\operatorname{sgn}\mathrm{Res}_x(p_m,\Phi_C)=(-1)^{\#\mathrm{SAT}(C)};$$
--   4. both polynomials have positive degree;
--   5. the $2^m$ roots of $p_m$ are real and simple, and $p_m$ depends only on $m$.
--
--   The resultant here is $\mathrm{Res}_x(f,g)=\mathrm{lc}(f)^{\deg g}\prod_{f(\alpha)=0}g(\alpha)$, with the actual degrees. The theorem shows that the sign of a univariate resultant of exponential degree is hard when the polynomials are given succinctly.
--
--   **Formalization Note** The size constants are one absolute $K$, and the circuit for $p_m$ is a function of $m$ alone.
--
--   Differences from the source:
--   - reading: $O(m)$ and $O(m(m+s)+s)$ → $\le K\,m$ and $\le K\,(m(m+s)+s)$ for one constant $K$ and all $m,s\ge1$; reason: the standing assumption $m,s\ge1$ of Appendix E, under which the $O$-bounds are uniform.
--   - reading: "$p_m$ depends only on $m$" → the circuit produced for $p_m$ is $\mathrm{pc}(m)$ for a fixed function $\mathrm{pc}$; reason: the statement is about the constructed circuits.
--   - reading: "$\operatorname{sgn}\mathrm{Res}=(-1)^{\#\mathrm{SAT}(C)}$" → positive when $\#\mathrm{SAT}(C)$ is even and negative when it is odd; reason: the same statement, since the resultant is nonzero.
--   - reading: "the $2^m$ roots of $p_m$ are real and simple" → $p_m$ has $2^m$ real roots counted with multiplicity, all distinct; reason: the same statement for a polynomial of degree $2^m$.
--   - encoding: "time polynomial in $m+s$" → polynomial time in the length of a Boolean-circuit code that writes $m$ in unary; reason: that code length is between $m+s$ and a polynomial in $m+s$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem E.1, p.45

import Mathlib
import Definitions.Def_ResultantVNP_Supplement_Reductions
import Definitions.Def_ResultantVNP_Supplement_CFCircuit
import Definitions.Def_ResultantVNP_Supplement_BoolCircuit

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Theorem E.1.** The negative and positive resultant-sign problems for univariate integer
polynomials given by constant-free arithmetic circuits are ⊕P-hard under deterministic
polynomial-time many-one reductions, even with the promise that the resultant is nonzero. More
precisely, from a Boolean circuit `C` on `m` inputs with `s` gates one can construct, in time
polynomial in `m + s`, constant-free circuits for `p_m, Φ_C ∈ ℤ[x]` such that `p_m = T_{2^m}`,
`size(p_m) = O(m)`, `Res_x(p_m, Φ_C) ≠ 0`, `size(Φ_C) = O(m(m + s) + s)`,
`sgn Res_x(p_m, Φ_C) = (−1)^{#SAT(C)}`. Both polynomials have positive degree. The `2^m` roots of
`p_m` are real and simple, and `p_m` depends only on `m`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem E.1, p.45 (proof pp.45–47).

**Formalization Note** `Res_x` is Mathlib's `Polynomial.resultant` with the actual degrees,
`Res(f, g) = lc(f)^{deg g} ∏_{f(α)=0} g(α)`. (1), (2): for every ⊕P language `L` a polynomial-time
`u` maps each `x` to a pair of circuits of positive degree with nonzero resultant (the promise),
negative, resp. positive, exactly when `x ∈ L`. (3): one constant `K`, one circuit `pc m` per `m`
(so `p_m` depends only on `m`) and one polynomial-time map `F` on circuit codes such that for every
Boolean circuit with `m ≥ 1` inputs and `s ≥ 1` gates (the standing assumption of Appendix E) all
listed properties hold; `sgn Res = (−1)^{#SAT}` is "positive for even, negative for odd `#SAT`";
"real and simple" is: the image of `p_m` in `ℝ[x]` has `2^m` real roots counted with multiplicity,
all distinct. -/
theorem theorem_E_1 :
    (∀ L ∈ ParityP, ∃ u : Word → Word, FunctionInP u ∧ ∀ x : Word,
      ∃ P Q : CFCircuit, u x = pairW P.encode Q.encode ∧
        0 < P.value.natDegree ∧ 0 < Q.value.natDegree ∧
        Polynomial.resultant P.value Q.value ≠ 0 ∧
        (x ∈ L ↔ Polynomial.resultant P.value Q.value < 0)) ∧
    (∀ L ∈ ParityP, ∃ u : Word → Word, FunctionInP u ∧ ∀ x : Word,
      ∃ P Q : CFCircuit, u x = pairW P.encode Q.encode ∧
        0 < P.value.natDegree ∧ 0 < Q.value.natDegree ∧
        Polynomial.resultant P.value Q.value ≠ 0 ∧
        (x ∈ L ↔ 0 < Polynomial.resultant P.value Q.value)) ∧
    ∃ (K : ℕ) (pc : ℕ → CFCircuit) (F : Word → Word), FunctionInP F ∧
      ∀ C : BoolCircuit, 1 ≤ C.m → 1 ≤ C.size →
        ∃ Φ : CFCircuit, F C.encode = pairW (pc C.m).encode Φ.encode ∧
          (pc C.m).value = Polynomial.Chebyshev.T ℤ ((2 : ℤ) ^ C.m) ∧
          (pc C.m).size ≤ K * C.m ∧
          Polynomial.resultant (pc C.m).value Φ.value ≠ 0 ∧
          Φ.size ≤ K * (C.m * (C.m + C.size) + C.size) ∧
          (Even C.numSat → 0 < Polynomial.resultant (pc C.m).value Φ.value) ∧
          (Odd C.numSat → Polynomial.resultant (pc C.m).value Φ.value < 0) ∧
          0 < (pc C.m).value.natDegree ∧ 0 < Φ.value.natDegree ∧
          ((pc C.m).value.map (Int.castRingHom ℝ)).roots.card = 2 ^ C.m ∧
          ((pc C.m).value.map (Int.castRingHom ℝ)).roots.Nodup := by sorry

end Supplement

end ResultantVNP

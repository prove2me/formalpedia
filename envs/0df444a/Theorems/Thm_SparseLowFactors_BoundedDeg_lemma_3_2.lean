-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_3_2
-- name    : SparseLowFactors.BoundedDeg.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:52.973975+00:00
-- url     : https://prove2.me/theorems/277da091-88cc-46da-8de2-91c714fd3dd8
-- title:
--   Lemma 3.2 — a deterministic poly($n$, $d!$, $s^d$)-time Hensel-ready point for the normalization
-- statement:
--   Let $F$ be a field with $\mathrm{char}\,F=0$ or $>d$, and let $f(X,Y)\in F[X,Y]$ be a non-zero $s$-sparse polynomial of individual degree at most $d$, with normalization $\hat f$ with respect to $Y$. There is a deterministic algorithm that, given $f$, runs in time $\mathrm{poly}(n,d!,s^d)$ and finds $\alpha\in F^n$ such that $\hat f$ is Hensel-ready at $X=\alpha$.
--
--   Formally: there are a universal $C$ and a fixed program $P$ such that for every such $F$ that is infinite or has $|F|>C(n+s^d+d!)^C$, every $w\ge C\log_2(n+s^d+d!+2)$, every oracle and admissible enumeration, every such $f$ and every listing of its terms, $P$ halts within $C(n+d!+s^d)^C$ steps without calling `factor`, and the field cells $F[W[0]],\dots,F[W[0]+n-1]$ at halting hold a point $\alpha$ at which $\hat f$ is Hensel-ready.
--
--   This is the preprocessing step of the factoring subroutine: after the shift $X\mapsto X+\alpha$, Hensel's lemma applies at the origin.
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - reading: standing convention "the field we are working over is sufficiently large" (p. 15) → hypothesis: F infinite or |F| > C·(…)^C with the universal C; reason: the convention is stated once for the whole paper; the statement is the paper's over a large field
--   - encoding: no univariate factoring in the algorithm → the program makes no `factor` call (and is quantified over every oracle); reason: the printed time bound has no T(F, d) term
--   - reading: "s-sparse polynomial of individual degree d" → individual degree at most d; reason: p. 15 defines "individual degree d" as degree at most d in each variable
--   - reading: f arbitrary → f ≠ 0; reason: the normalization is defined only when f_d ≠ 0 (p. 16)
--   - encoding: f(X, Y) "an n-variate polynomial" → f has variables Y = X_0 and X_1,…,X_n (n + 1 variables), viewed in F[X][Y] by finSuccEquiv; reason: index convention; poly(n) bounds are unchanged up to the universal constant
--   - encoding: f given in monomial representation; output list/values → f is given as its terms in any order (exponents in word cells, coefficients in field cells); outputs are read from the memory at halting through the fixed layout of the Machine definition; reason: a machine statement needs a concrete layout; any order of terms is allowed
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 28, Lemma 3.2

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Normalization
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

namespace SparseLowFactors.BoundedDeg

theorem lemma_3_2 :
    ∃ C : ℕ, ∃ P : List Instr,
    ∀ (F : Type) [Field F] (n s d : ℕ),
      (ringChar F = 0 ∨ d < ringChar F) →
      (Infinite F ∨ C * (n + s ^ d + d.factorial) ^ C < Nat.card F) →
      ∀ w : ℕ, C * Nat.log 2 (n + s ^ d + d.factorial + 2) ≤ w →
      ∀ fac : FactorOracle F, ∀ e : ℕ → F, EnumOK e →
      ∀ f : MvPolynomial (Fin (n + 1)) F, f ≠ 0 → IsSparse s f → IndDegLE d f →
      ∀ terms : List (F × (Fin (n + 1) → ℕ)), IsSparseRep f terms →
      ∃ (T : ℕ) (r : Result F w),
        run P fac e T (loadWords w (sparseWords [(n : ℤ), (s : ℤ), (d : ℤ)] terms))
          (loadFields (sparseFields terms)) = some r ∧
        T ≤ C * (n + d.factorial + s ^ d) ^ C ∧
        r.facCalls = 0 ∧
        HenselReady (normalize (MvPolynomial.finSuccEquiv F n f))
          (MvPolynomial.eval fun i : Fin n => r.fm (outPtr r.wm + (i : ℤ))) := by sorry

end SparseLowFactors.BoundedDeg

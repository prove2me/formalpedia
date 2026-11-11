-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_3_1
-- name    : SparseLowFactors.BoundedDeg.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:45.19087+00:00
-- url     : https://prove2.me/theorems/fa1b118c-a82a-4dbc-8863-c499334ba43c
-- title:
--   Lemma 3.1 — a list of $\le 2^d-1$ constant-depth circuits containing every non-constant factor of the normalization
-- statement:
--   Let $F$ be a field with $\mathrm{char}\,F=0$ or $>d$, and let $f(X,Y)\in F[X,Y]$ be non-zero, with sparsity at most $s$ and individual degree at most $d$; let $\hat f$ be its normalization with respect to $Y$. There is an algorithm running in time $\mathrm{poly}(s^d,d!,n,T(F,d))$ that outputs a list $L$ with
--
--   1. $|L|\le2^d-1$;
--   2. every element of $L$ a circuit over $F$ of size $\mathrm{poly}(n,s,d)$ and depth $O(1)$;
--   3. every non-constant factor $\hat g$ of $\hat f$ computed (up to a non-zero scalar) by some circuit of $L$;
--
--   and it also outputs the $Y$-degree of the polynomial computed by every circuit in $L$. The list may contain spurious candidates.
--
--   Formally: universal $C,\Delta$ and a fixed program $P$ such that for every such $F$ that is infinite or has $|F|>C(n+s^d+d!)^C$, every $w\ge C\log_2(n+s^d+d!+2)$, every valid oracle and admissible enumeration, every such $f$ and every listing of its terms, $P$ halts within $C(s^d+d!+n)^C$ steps with `factor` calls of degree at most $d$ only, and its output decodes to such a list with sizes $\le C(n+s+d)^C$, depths $\le\Delta$, and the $Y$-degrees in the words after the list.
--
--   This is the factoring subroutine for normalized polynomials used at every step of the recursion of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - encoding: time poly(…)·T(F, d) / T(F, d) suppressed → each univariate factorization is one `factor` step against an adversarial valid oracle, and every call has degree at most d; reason: Remarks 1.2, 4.2 and Definition 2.11 make univariate factoring a black box of cost T(F, d)
--   - reading: standing convention "the field we are working over is sufficiently large" (p. 15) → hypothesis: F infinite or |F| > C·(…)^C with the universal C; reason: the convention is stated once for the whole paper; the statement is the paper's over a large field
--   - reading: "every … factor … is computed by some circuit in L" → for every such factor g some circuit computes c·g with c ≠ 0; reason: as printed the claim fails for scalar multiples of one factor (finding I1); the proofs list monic factors
--   - reading: f arbitrary → f ≠ 0; reason: the normalization is defined only when f_d ≠ 0 (p. 16)
--   - reading: "non-constant factor" → factor of positive total degree; reason: constant factors are excluded by the source
--   - encoding: "the algorithm can compute the Y-degree of … every circuit in L" → word cell W[W[0] + 1 + |L| + k] holds the Y-degree of the k-th circuit's polynomial; reason: output layout
--   - encoding: f(X, Y) "an n-variate polynomial" → f has variables Y = X_0 and X_1,…,X_n (n + 1 variables), viewed in F[X][Y] by finSuccEquiv; reason: index convention; poly(n) bounds are unchanged up to the universal constant
--   - encoding: f given in monomial representation; output list/values → f is given as its terms in any order (exponents in word cells, coefficients in field cells); outputs are read from the memory at halting through the fixed layout of the Machine definition; reason: a machine statement needs a concrete layout; any order of terms is allowed
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 27, Lemma 3.1

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Normalization
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

open SetMultCost

namespace SparseLowFactors.BoundedDeg

theorem lemma_3_1 :
    ∃ C Δ : ℕ, ∃ P : List Instr,
    ∀ (F : Type) [Field F] (n s d : ℕ),
      (ringChar F = 0 ∨ d < ringChar F) →
      (Infinite F ∨ C * (n + s ^ d + d.factorial) ^ C < Nat.card F) →
      ∀ w : ℕ, C * Nat.log 2 (n + s ^ d + d.factorial + 2) ≤ w →
      ∀ fac : FactorOracle F, fac.Valid → ∀ e : ℕ → F, EnumOK e →
      ∀ f : MvPolynomial (Fin (n + 1)) F, f ≠ 0 → IsSparse s f → IndDegLE d f →
      ∀ terms : List (F × (Fin (n + 1) → ℕ)), IsSparseRep f terms →
      ∃ (T : ℕ) (r : Result F w),
        run P fac e T (loadWords w (sparseWords [(n : ℤ), (s : ℤ), (d : ℤ)] terms))
          (loadFields (sparseFields terms)) = some r ∧
        T ≤ C * (s ^ d + d.factorial + n) ^ C ∧
        r.facMaxDeg ≤ d ∧
        ∃ L : List (Circuit (Fin (n + 1)) F),
          decodeList r.wm (outPtr r.wm) (decodeCircuit (n + 1) r.wm r.fm) = some L ∧
          L.length ≤ 2 ^ d - 1 ∧
          (∀ Φ ∈ L, Φ.size ≤ C * (n + s + d) ^ C ∧ depth Φ ≤ Δ) ∧
          (∀ g : Polynomial (MvPolynomial (Fin n) F), g ∣ normalize (MvPolynomial.finSuccEquiv F n f) →
            0 < ((MvPolynomial.finSuccEquiv F n).symm g).totalDegree →
            ∃ Φ ∈ L, ∃ c : F, c ≠ 0 ∧ Φ.value = c • (MvPolynomial.finSuccEquiv F n).symm g) ∧
          ∀ k : ℕ, ∀ hk : k < L.length,
            (r.wm (outPtr r.wm + 1 + (L.length : ℤ) + (k : ℤ))).toNat = (L[k]'hk).value.degreeOf 0 := by sorry

end SparseLowFactors.BoundedDeg

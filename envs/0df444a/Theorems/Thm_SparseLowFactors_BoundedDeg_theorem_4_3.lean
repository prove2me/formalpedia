-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_theorem_4_3
-- name    : SparseLowFactors.BoundedDeg.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:40.488905+00:00
-- url     : https://prove2.me/theorems/e6c5f39f-9082-464b-a815-a34a2d09ce74
-- title:
--   Theorem 4.3 (recursive algorithm) — an $s^d$-size list of constant-depth circuits with division gates, monomial-equivalent to every factor
-- statement:
--   Let $f\in F[X_1,\dots,X_n]$ be a non-zero $s$-sparse polynomial of individual degree at most $d$, $\mathrm{char}\,F=0$ or $>d$. There is an algorithm running in time $\mathrm{poly}(s^d,d!,n)$ (univariate factoring of degree at most $d$ at unit cost) that outputs a list $L_{\mathrm{mon}}$ of at most $s^d$ circuits with division gates, each over $F$ of size $\mathrm{poly}(s^d,n,d)$ and depth $O(1)$, such that for **every** factor $g$ of $f$ there is a polynomial $h$ computed by some circuit of $L_{\mathrm{mon}}$ with
--   $$c\,g\ \prec_d\ h\qquad\text{for some } c\in F\setminus\{0\},$$
--   i.e. $h=c\,g\,M$ for a monomial $M$ of individual degree at most $d$.
--
--   Formally: universal $C,\Delta$ and a fixed program, as in Lemma 3.1, halting within $C(s^d+d!+n)^C$ steps on $(n,s,d)$ and the terms of $f$, whose output decodes to such a list with sizes $\le C(s^d+n+d)^C$ and depths $\le\Delta$.
--
--   This is Algorithm 1; Theorem 1.1 follows by stripping the monomial and eliminating divisions (Corollary 2.31, Lemma 2.32).
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - encoding: time poly(s^d, d!, n) (factoring through Lemma 3.1) → each univariate factorization is one `factor` step against an adversarial valid oracle, every call of degree at most d; reason: Remark 4.2: the time is poly(s^d, d!, n)·T(F, d)
--   - reading: standing convention "the field we are working over is sufficiently large" (p. 15) → hypothesis: F infinite or |F| > C·(…)^C with the universal C; reason: the convention is stated once for the whole paper; the statement is the paper's over a large field
--   - reading: "there exists a polynomial h computed by some circuit in Lmon such that g ≺_d h" → … such that (c·g) ≺_d h for some c ≠ 0; reason: as printed the claim fails for the factors 1 and 2 of X_1 (finding I1)
--   - reading: f arbitrary → f ≠ 0; reason: the zero polynomial has infinitely many pairwise non-associate factors (finding I2); "the maximal monomial divisor of f" presupposes f ≠ 0
--   - encoding: "h computed by a circuit with division gates" → the circuit has no zero denominator and its rational function equals h; reason: Definition 2.5: the rational function is promised to equal a polynomial
--   - encoding: f given in monomial representation; output list/values → f is given as its terms in any order (exponents in word cells, coefficients in field cells); outputs are read from the memory at halting through the fixed layout of the Machine definition; reason: a machine statement needs a concrete layout; any order of terms is allowed
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 33, Theorem 4.3

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

namespace SparseLowFactors.BoundedDeg

theorem theorem_4_3 :
    ∃ C Δ : ℕ, ∃ P : List Instr,
    ∀ (F : Type) [Field F] (n s d : ℕ),
      (ringChar F = 0 ∨ d < ringChar F) →
      (Infinite F ∨ C * (n + s ^ d + d.factorial) ^ C < Nat.card F) →
      ∀ w : ℕ, C * Nat.log 2 (n + s ^ d + d.factorial + 2) ≤ w →
      ∀ fac : FactorOracle F, fac.Valid → ∀ e : ℕ → F, EnumOK e →
      ∀ f : MvPolynomial (Fin n) F, f ≠ 0 → IsSparse s f → IndDegLE d f →
      ∀ terms : List (F × (Fin n → ℕ)), IsSparseRep f terms →
      ∃ (T : ℕ) (r : Result F w),
        run P fac e T (loadWords w (sparseWords [(n : ℤ), (s : ℤ), (d : ℤ)] terms))
          (loadFields (sparseFields terms)) = some r ∧
        T ≤ C * (s ^ d + d.factorial + n) ^ C ∧
        r.facMaxDeg ≤ d ∧
        ∃ L : List (DivCircuit (Fin n) F),
          decodeList r.wm (outPtr r.wm) (decodeDivCircuit n r.wm r.fm) = some L ∧
          L.length ≤ s ^ d ∧
          (∀ Φ ∈ L, Φ.size ≤ C * (s ^ d + n + d) ^ C ∧ Φ.depth ≤ Δ) ∧
          ∀ g : MvPolynomial (Fin n) F, g ∣ f →
            ∃ Φ ∈ L, ∃ h : MvPolynomial (Fin n) F, Φ.Computes h ∧
              ∃ c : F, c ≠ 0 ∧ PrecR d (c • g) h := by sorry

end SparseLowFactors.BoundedDeg

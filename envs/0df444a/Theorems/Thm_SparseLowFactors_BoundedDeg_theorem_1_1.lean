-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_theorem_1_1
-- name    : SparseLowFactors.BoundedDeg.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:44.358216+00:00
-- url     : https://prove2.me/theorems/f3d6c2e4-109b-4956-86b2-0ee5a7387774
-- title:
--   Theorem 1.1 (Main Theorem 1) — a deterministic poly($s^d$, $d!$, $n$)-time list of $s^d$ constant-depth circuits containing every factor not divisible by a monomial
-- statement:
--   Let $F$ be a field with $\mathrm{char}\,F=0$ or $\mathrm{char}\,F>d$, and let $f\in F[X_1,\dots,X_n]$ be a non-zero $s$-sparse polynomial of individual degree at most $d$. The **maximal monomial divisor** of $f=\sum_jc_jX^{\alpha_j}$ is $\prod_iX_i^{\min_j\alpha_{j,i}}$, and a factor $g$ of $f$ is **not divisible by a monomial** if no variable divides it.
--
--   There are universal constants $C,\Delta$ and one fixed program $P$ for the deterministic algebraic RAM with univariate factorization such that the following holds for every such $F,n\ge1,s\ge1,d\ge0,f$, for every field $K\supseteq F$ that is infinite or has $|K|>C(n+s^d)^C$ (in particular $K=F$ when $F$ is that large), every word length $w\ge C\log_2(n+s^d+d!+2)$, every valid factorization oracle and admissible enumeration over $K$, and every listing of the terms of $f$. Run over $K$ on $(n,s,d)$ and the sparse representation of $f$, $P$ halts within
--   $$C\,(s^d+d!+n)^C$$
--   steps, calls the factorization oracle only on polynomials of degree at most $d$, and outputs
--
--   1. the exponent vector $(\min_j\alpha_{j,1},\dots,\min_j\alpha_{j,n})$ of the maximal monomial divisor of $f$, and
--   2. a list $L$ of at most $s^d$ division-free circuits over $K$, each of size at most $C(s^d+n)^C$ and depth at most $\Delta$,
--
--   such that for every $g\in F[X]$ with $g\mid f$ and no $X_i$ dividing $g$, some circuit in $L$ computes $c\cdot g$ for a non-zero $c\in K$.
--
--   This is the paper's first main result: factoring bounded-individual-degree sparse polynomials reduces, deterministically and in polynomial time for constant $d$, to univariate factoring, up to spurious list entries.
--
--   **Formalization Note** The machine, the oracle quantification and the layouts are those of the Machine definition; circuits are `SetMultCost_Circuit` with the depth of the Circuits definition. Circuits compute polynomials in $K[X]$, compared with $g$ mapped into $K[X]$. The extension $K$ is the paper's Remark 1.3; with $K=F$ the circuits are over $F$.
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - encoding: time poly(…)·T(F, d) / T(F, d) suppressed → each univariate factorization is one `factor` step against an adversarial valid oracle, and every call has degree at most d; reason: Remarks 1.2, 4.2 and Definition 2.11 make univariate factoring a black box of cost T(F, d)
--   - reading: "if |F| > poly(n, s^d) the circuits are over F" and Remark 1.3 ("we just work over a suitable field extension") → the program runs over any field K ⊇ F that is infinite or has |K| > C(n + s^d)^C; the input is over F and the factors range over F[X]; K = F is allowed whenever F is that large; reason: this is how the theorem covers every field of characteristic 0 or > d, small ones included
--   - reading: "every … factor … is computed by some circuit in L" → for every such factor g some circuit computes c·g with c ≠ 0; reason: as printed the claim fails for scalar multiples of one factor (finding I1); the proofs list monic factors
--   - reading: f arbitrary → f ≠ 0; reason: the zero polynomial has infinitely many pairwise non-associate factors (finding I2); "the maximal monomial divisor of f" presupposes f ≠ 0
--   - reading: "factor of f that is not divisible by a monomial" → g ∣ f and no variable X_i divides g (nonzero constants included); reason: divisibility by a non-constant monomial is divisibility by some X_i
--   - encoding: "outputs the maximal monomial divisor of f" → outputs its exponent vector (min_j α_{j,i})_i, read from W[W[0] + i]; reason: Remark 1.4 gives the monomial by its exponents
--   - encoding: f given in monomial representation; output list/values → f is given as its terms in any order (exponents in word cells, coefficients in field cells); outputs are read from the memory at halting through the fixed layout of the Machine definition; reason: a machine statement needs a concrete layout; any order of terms is allowed
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
--   - encoding: n, s, d → n ≥ 1, s ≥ 1, d ≥ 0, and n, s, d are part of the input; reason: the paper's parameters; s ≥ 1 is implied by f ≠ 0
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 5, Theorem 1.1 (Main Theorem 1), with Remarks 1.2–1.4; restated as Theorem 4.1 with Remark 4.2, p. 33

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

open SetMultCost

namespace SparseLowFactors.BoundedDeg

theorem theorem_1_1 :
    ∃ C Δ : ℕ, ∃ P : List Instr,
    ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (n s d : ℕ),
      1 ≤ n → 1 ≤ s →
      (ringChar F = 0 ∨ d < ringChar F) →
      (Infinite K ∨ C * (n + s ^ d) ^ C < Nat.card K) →
      ∀ w : ℕ, C * Nat.log 2 (n + s ^ d + d.factorial + 2) ≤ w →
      ∀ fac : FactorOracle K, fac.Valid → ∀ e : ℕ → K, EnumOK e →
      ∀ f : MvPolynomial (Fin n) F, f ≠ 0 → IsSparse s f → IndDegLE d f →
      ∀ terms : List (F × (Fin n → ℕ)), IsSparseRep f terms →
      ∃ (T : ℕ) (r : Result K w),
        run P fac e T (loadWords w (sparseWords [(n : ℤ), (s : ℤ), (d : ℤ)] terms))
          (loadFields (sparseFields terms)) = some r ∧
        T ≤ C * (s ^ d + d.factorial + n) ^ C ∧
        r.facMaxDeg ≤ d ∧
        (∀ i : Fin n, (r.wm (outPtr r.wm + (i : ℤ))).toNat = monDivExp f i) ∧
        ∃ L : List (Circuit (Fin n) K),
          decodeList r.wm (outPtr r.wm + n) (decodeCircuit n r.wm r.fm) = some L ∧
          L.length ≤ s ^ d ∧
          (∀ Φ ∈ L, Φ.size ≤ C * (s ^ d + n) ^ C ∧ depth Φ ≤ Δ) ∧
          ∀ g : MvPolynomial (Fin n) F, g ∣ f → NoMonomialDivisor g →
            ∃ Φ ∈ L, ∃ c : K, c ≠ 0 ∧
              Φ.value = c • MvPolynomial.map (algebraMap F K) g := by sorry

end SparseLowFactors.BoundedDeg

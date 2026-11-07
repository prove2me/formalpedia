-- Prove2me | Theorems.Thm_RevisitXor_theorem_1
-- name    : RevisitXor.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:14.361201+00:00
-- url     : https://prove2.me/theorems/c73b0941-7581-464c-be50-f42dfaa0fbd5
-- title:
--   Theorem 1 — some $f$ has correlation $\le c\,2^{-n/2}\log(2^{n/2}|S|)$ with $S$, yet $f^{\oplus k}$ correlates $(2^{-n/2})^{k/2}$ with a quadratic polynomial
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $n$ and $k$ be even and let $S$ be a set of functions from $[2]^n$ to $[2]$. There is $f:[2]^n\to[2]$ such that
--
--   1. $f$ has correlation at most $2^{-n/2}\cdot c\log(2^{n/2}\cdot|S|)$ with every function in $S$:
--   $$\operatorname{corr}(f,g)\le 2^{-n/2}\cdot c\log\big(2^{n/2}|S|\big)\qquad(g\in S);$$
--   2. if $n\ge2$, the same bound holds for $|\operatorname{corr}(f,g)|$, $g\in S$;
--   3. $f^{\oplus k}$ has correlation at least $(2^{-n/2})^{k/2}$ with some quadratic polynomial $p$ modulo $2$ in the $kn$ variables of $[2]^{kn}$:
--   $$\operatorname{corr}\big(f^{\oplus k},p\big)\ge\big(2^{-n/2}\big)^{k/2}.$$
--
--   Taking $S$ to be the functions computed by circuits of size $n^a$ refutes the "dream XOR lemma" of Goldreich, Nisan and Wigderson: $f$ has correlation about $n^{-10a}$ with such circuits on a suitable input length, while $f\oplus f$ correlates $n^{-10a}$ with a quadratic polynomial, so the correlation does not decay to $\epsilon^2$ at almost no loss in size. It also shows that there is no XOR lemma with strong decay for low-degree polynomials that holds for every function.
--
--   **Formalization Note** $\log$ is the natural logarithm and $|S|$ the number of elements; when $S=\emptyset$, $\log 0=0$ and items 1–2 are vacuous. $2^{-n/2}$ is $(2^{n/2})^{-1}$ with $n/2$ an exact natural number. $[2]^{kn}$ is curried as $([2]^n)^k$; a polynomial in its $kn$ variables is an `MvPolynomial (Fin k × Fin n) (ZMod 2)` evaluated at $x_j(i)$, and "quadratic" means total degree at most $2$.
--
--   Differences from the source:
--   - generalization: correlation ≤ 2^{−n/2}·c log(2^{n/2}·|S|) with any function in S (signed, p.1) → in addition |corr(f, g)| ≤ the same bound for every g ∈ S when n ≥ 2; reason: the |·| reading of p.6, which the proof gives by its union bound over 2|S| functions (h and h ⊕ 1); an added conjunct, so the statement specializes to the printed one; at n = 0 the |·| form is false (S = {0}: |corr(f, 0)| = 1 for every f, bound 0)
--   - reading: a quadratic polynomial modulo 2 in kn variables → an MvPolynomial over ZMod 2 in the variables Fin k × Fin n with total degree ≤ 2; reason: degree-d polynomials means degree at most d; for n = 0 or k = 0 there are no variables and degree exactly 2 is impossible; the proof's witness x·y′ + x′·y has degree exactly 2 when n, k ≥ 2
--   - encoding: c, log and |S| in 2^{−n/2}·c log(2^{n/2}·|S|) → one absolute c > 0 chosen before n, k, S; Real.log; S.card for S a Finset, with log 0 = 0 at |S| = 0; reason: p.1 convention on c; another base of log changes only c; every set of functions [2]^n → [2] is finite
--   - encoding: [2]^{kn} and 2^{−n/2} for even n, k → Fin k → Fin n → ZMod 2 with variables indexed by Fin k × Fin n; ((2:ℝ)^(n/2))⁻¹ raised to the ℕ-power k/2; reason: same points and values, n and k being even
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 1, p.2

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_RevisitXor_xorPow

namespace RevisitXor

/-- **Theorem 1 (counterexample to the dream XOR lemma).** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Theorem 1, p.2: "Let n and k be even and let S be a set of functions from [2]^n to
[2]. There is f : [2]^n → [2] that has correlation ≤ 2^{−n/2} · c log(2^{n/2} · |S|) with any
function in S, but f^{⊕k} has correlation ≥ (2^{−n/2})^{k/2} with a quadratic polynomial modulo 2
in kn variables."

**Formalization Note.**
* `c` is one absolute constant, chosen before `n`, `k` and `S` (p.1: "Every occurrence of “c”
  denotes a possibly different real > 0"). `log` is the natural logarithm (another base changes
  only `c`); `|S|` is `S.card`, and every set of functions `[2]^n → [2]` is finite. At `|S| = 0`
  Lean's `log 0 = 0` and the first two clauses are vacuous.
* `n`, `k` even, including `0`; `2^{-n/2}` is `((2:ℝ)^(n/2))⁻¹` with exact ℕ-division.
* Correlation is the signed average of p.1 (`corr`). Clause (a) is the printed bound. Clause (b)
  adds the bound on `|corr f g|` when `2 ≤ n`; it is false at `n = 0` (`S = {0}`: every `f` has
  `|corr f 0| = 1` while the bound is `0`).
* `[2]^{kn}` is curried as `Fin k → [2]^n`; its `kn` variables are indexed by `Fin k × Fin n`
  and evaluated at `x j i`. "Quadratic polynomial modulo 2" is an `MvPolynomial` over `ZMod 2` of
  total degree at most `2`. -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, Even n → Even k → ∀ S : Finset (Cube n → ZMod 2),
      ∃ f : Cube n → ZMod 2,
        (∀ g ∈ S, corr f g ≤
          ((2 : ℝ) ^ (n / 2))⁻¹ * (c * Real.log ((2 : ℝ) ^ (n / 2) * S.card))) ∧
        (2 ≤ n → ∀ g ∈ S, |corr f g| ≤
          ((2 : ℝ) ^ (n / 2))⁻¹ * (c * Real.log ((2 : ℝ) ^ (n / 2) * S.card))) ∧
        ∃ p : MvPolynomial (Fin k × Fin n) (ZMod 2), p.totalDegree ≤ 2 ∧
          (((2 : ℝ) ^ (n / 2))⁻¹) ^ (k / 2) ≤
            corr (xorPow f k) (fun x => MvPolynomial.eval (fun ji => x ji.1 ji.2) p) := by sorry

end RevisitXor

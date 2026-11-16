-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_Supplement_kopparty_reconstruction
-- name    : RSCapacity.ListDecoding.Supplement.kopparty_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:19:27.992762+00:00
-- url     : https://prove2.me/theorems/f30fea0b-b140-4f75-ac9e-9093dfc97113
-- title:
--   Lemma 6.6 — Kopparty reconstruction by rational functions with degree bounds (corrected: $a_i=f^{(i)}(\gamma)$ for $0\le i<k$)
-- statement:
--   Let $F$ be a field and $k,d\ge0$. Let $P\in F[Z,X,Y_0,\dots,Y_d]$ be a nonzero polynomial with $\operatorname{TopVar}(P)=j\le d$, i.e. $P$ depends non-trivially on $Y_j$ and on no $Y_i$ with $i>j$. Assume
--
--   $$\operatorname{char}(F)>\max\bigl(k,\deg_{Y_i}P\bigr)\quad\text{for all } 0\le i\le d.$$
--
--   Then there are polynomials $N_{P,i}\in F[Z,X,Y_0,\dots,Y_d]$ and integers $e_i\ge0$ $(d<i<k)$ with
--
--   $$\deg N_{P,i}\le 2(i-j)\deg P,\qquad e_i\le 2(i-j),$$
--
--   where $\deg$ is the total degree in $Z,X,Y_0,\dots,Y_d$, such that the rational functions $\Phi_{P,i}=Y_i$ for $0\le i\le d$ and $\Phi_{P,i}=N_{P,i}/(\partial_{Y_j}P)^{2e_i}$ for $d<i<k$ have the following property. Suppose $\zeta\in F$ satisfies $\operatorname{TopVar}(P|_{Z=\zeta})=j$, $f\in F[X]$ has degree less than $k$, $\gamma\in F$, and $a_i=f^{(i)}(\gamma)$ is the $i$-th Hasse derivative of $f$ at $\gamma$, such that
--
--   1. $P(\zeta,X,f,f^{(1)},\dots,f^{(d)})=0$, and
--   2. $(\partial_{Y_j}P)(\zeta,\gamma,a_0,\dots,a_d)\ne0$.
--
--   Then for all $0\le i<k$,
--
--   $$a_i=\Phi_{P,i}(\zeta,\gamma,a_0,\dots,a_d),\qquad\text{and consequently}\qquad f(X)=\sum_{i=0}^{k-1}\Phi_{P,i}(\zeta,\gamma,a_0,\dots,a_d)\,(X-\gamma)^i.$$
--
--   The functions $\Phi_{P,i}$ depend only on $P$ (and $k$), not on $\zeta$, $\gamma$ or $f$. The first $d+1$ Taylor coefficients of a solution therefore determine it through explicit rational functions of polynomially bounded degree; in Section 6 this places every pair $(\zeta,f)$ with many agreements in the image of a low-degree rational map, which bounds the exceptional $\zeta$ in Theorem 1.2.
--
--   **Formalization Note** Variables are indexed by `Fin (d+3)` ($0=Z$, $1=X$, $i+2=Y_i$); $P(\zeta,X,f,\dots)$ is the published `differentialSubstitute` applied to $P|_{Z=\zeta}$. $\operatorname{char}(F)$ is Lean's `ringChar F`, so the hypothesis requires positive characteristic exactly as the printed inequality does. A rational function is represented by its numerator $N_{P,i}$ and exponent $e_i$; its value is taken only at points where condition 2 makes the denominator nonzero. Since $\deg f<k$, $a_i=f^{(i)}(\gamma)=0$ for $i\ge k$, which is how $a_k,\dots,a_d$ are read when $d\ge k$.
--
--   Differences from the source:
--   - correction: "a_i = f^{(i)}(γ) for 0 < i < k" (a_0 unconstrained) → a_i = f^{(i)}(γ) for every 0 ≤ i < k; reason: the printed range is false — d = 0, k = 2, P = Y_0² − X² over any field of characteristic ≥ 3 (so char > max(2, deg_{Y_0}P = 2)), j = 0, TopVar(P|_{Z=ζ}) = 0 for every ζ; f = X and f = −X both solve P(ζ,X,f) = 0, and with γ = 1 and the free value a_0 = 1 the denominator (∂_{Y_0}P)(ζ,1,1) = 2 ≠ 0 in both cases, yet a_1 = 1 for f = X and a_1 = −1 for f = −X, so no single Φ_{P,1}(ζ,1,1) can equal both; with a_0 = f(γ) (as in the proof, Appendix C p.28, "a_i = f^{(i)}(γ)") the statement is the one proved
--   - reading: a_0, …, a_d with a_i defined only for i < k → a_i := f^{(i)}(γ) for all 0 ≤ i ≤ d (equal to 0 for k ≤ i ≤ d); reason: the source leaves a_i for k ≤ i ≤ d undefined when d ≥ k; Hasse derivatives of order ≥ k of a degree-<k polynomial vanish, and the proof (p.28) defines a_i = f^{(i)}(γ) uniformly
--   - reading: "Consequently, f(X) = Σ Φ_{P,i}(a_0, …, a_d)(X − γ)^i" → Φ_{P,i}(ζ, γ, a_0, …, a_d); reason: Φ_{P,i} is a function of (Z, X, Y_0, …, Y_d) and the preceding sentence evaluates it at (ζ, γ, a_0, …, a_d)
--   - encoding: rational functions Φ_{P,i} = N_{P,i}/(∂_{Y_j}P)^{2e} → numerator polynomials N i and exponents e i, evaluated by field division at points where the denominator is nonzero; reason: same functions on their domain, and the property is asserted only there
--   - encoding: F[Z, X, Y_0, …, Y_d], deg, char(F), f^{(i)} → MvPolynomial (Fin (d+3)) F, totalDegree, ringChar F, Polynomial.hasseDeriv; reason: Lean conventions; same instances
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Lemma 6.6, p.21 (= Lemma C.1, p.27, proof pp.27–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Supplement_ProximityGaps

open scoped BigOperators

namespace RSCapacity.ListDecoding.Supplement

open RSCapacity.ListDecoding

/-- Lemma 6.6 (= Lemma C.1), submission #495 p.21 (restated p.27, proved pp.27–30),
with the minimal correction `aᵢ = f^{(i)}(γ)` for `0 ≤ i < k` (printed: `0 < i < k`).
Here `aᵢ := (hasseDeriv i f)(γ)` for every `i` (so `aᵢ = 0` for `k ≤ i ≤ d`),
`deg` is total degree in `Z, X, Y₀, …, Y_d`, and `Φ_{P,i}` is `reconstructionValue`.
The numerators `N`, exponents `e` are chosen from `P`, `k` only, before `ζ, γ, f`. -/
theorem kopparty_reconstruction {F : Type} [Field F] (k d : ℕ)
    (P : MvPolynomial (Fin (d + 3)) F) (hP : P ≠ 0) (j : Fin (d + 1))
    (hj : IsTopVar P varY j)
    (hchar : k < ringChar F ∧ ∀ i : Fin (d + 1), P.degreeOf (varY i) < ringChar F) :
    ∃ (N : ℕ → MvPolynomial (Fin (d + 3)) F) (e : ℕ → ℕ),
      (∀ i : ℕ, d < i → i < k →
        (N i).totalDegree ≤ 2 * (i - j.val) * P.totalDegree ∧ e i ≤ 2 * (i - j.val)) ∧
      ∀ (ζ γ : F) (f : Polynomial F),
        IsTopVar (specializeZ ζ P) Fin.succ j →
        f.degree < (k : WithBot ℕ) →
        differentialSubstitute (specializeZ ζ P) f = 0 →
        MvPolynomial.eval
            (zxyPoint ζ γ fun i : Fin (d + 1) => (Polynomial.hasseDeriv i.val f).eval γ)
            (MvPolynomial.pderiv (varY j) P) ≠ 0 →
        (∀ i : ℕ, i < k →
          (Polynomial.hasseDeriv i f).eval γ =
            reconstructionValue P j N e i
              (zxyPoint ζ γ fun i : Fin (d + 1) => (Polynomial.hasseDeriv i.val f).eval γ)) ∧
        f = ∑ i ∈ Finset.range k,
          Polynomial.C (reconstructionValue P j N e i
              (zxyPoint ζ γ fun i : Fin (d + 1) => (Polynomial.hasseDeriv i.val f).eval γ)) *
            (Polynomial.X - Polynomial.C γ) ^ i := by sorry

end RSCapacity.ListDecoding.Supplement

-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_12
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:50:12.80889+00:00
-- url     : https://prove2.me/theorems/2d349503-7f4b-437d-92e9-a145330ac7da
-- title:
--   Theorem 12 — One uniformly explicit prescribed-entropy family, independent of d, with (23), all asymptotic consequences and exact minimum sampling degree
-- statement:
--   Use the single deterministic multiscale family $U_{N,k}$ of Eq. (24), for every $0\le k\le N$, independently of $d$. It is flat of entropy $k$ and one deterministic bit algorithm samples it from exactly $k$ fair bits in time $C(N+1)^a$, with fixed $C,a$. Set $c=N-k$, $H=\min\{k,\sqrt c\}$ and $D=\lfloor\log_2H\rfloor$. If $H\ge2^{16}$, its minimum exact sampling degree is $D+1$, and for every $1\le d\le D$,
--   $$\mathcal O_d(U_{N,k})\le2^{-\frac1{256}\max\{H/2^d,w_d\min\{k/2^d,c/4^d\}\}},\quad w_d=D^{-1}+(d+1)^{-2}+(D-d+1)^{-2}.$$
--   For each fixed $d$, there are $a_d>0$ and a threshold, depending only on $d$, such that the same family has overlap at most $\exp(-a_d\min\{k,c\})$ beyond that threshold. Along every parameter sequence with $2^d=o(H)$ its overlap tends to zero. For each $0<\varepsilon<1$ it has overlap $2^{-\Omega(H^\varepsilon)}$ uniformly when $2^d\le H^{1-\varepsilon}$ and $H$ is sufficiently large. Uniformly for $1\le d\le D$ it has overlap $2^{-\Omega(\min\{k/2^d,c/4^d\}/\log_2H)}$. When also $k\le\sqrt c$, the explicit bound $2^{-k/(256\,2^d)}$ holds throughout this range. At degree zero the exact supremum is $2^{-k}$ for every $k\le N$.
--   All source suprema allow arbitrary seed length and outputs outside the target support. This companion theorem gives one prescribed-entropy family with all its finite and asymptotic guarantees.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
--   - encoding: uniform polynomial sampling and asymptotic clauses → one finite bit program with a C(N+1)^a bound, plus quantified eventual inequalities and sequential little-o; reason: all constants precede the dimensions and sources; the same deterministic quadratic-tower family is used in every clause
--   - generalization: there is a uniformly explicit family U_{N,k} → the specific family (24) of the proof, with the deterministic quadratic-tower bases of §2.5, and its exact degree-zero supremum 2^(−k) from the proof; reason: the proof constructs exactly this family, so the Lean statement witnesses the source's existential and implies every clause of it
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 12, printed p. 17; PDF p. 19

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Multiscale

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_12 :
    UniformlyPolynomial UniversalSampler ∧
    (∀ N k : ℕ, k ≤ N → Flat k (UniversalLaw N k)) ∧
    (∀ N k : ℕ, k ≤ N → BestOverlap 0 (UniversalLaw N k) = (2 : ℝ)^(-(k : ℤ))) ∧
    (∀ N k : ℕ, k ≤ N → (2 : ℝ)^16 ≤ ScaleH N k →
      MinimumDegree (Cutoff N k + 1) (UniversalLaw N k) ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ Cutoff N k →
        BestOverlap d (UniversalLaw N k) ≤
          (2 : ℝ) ^ (-(1/256 : ℝ) * max (ScaleH N k / (2 : ℝ)^d)
            ((Weight (Cutoff N k) d : ℝ) *
              min ((k : ℝ)/(2 : ℝ)^d) ((N-k : ℕ)/(4 : ℝ)^d)))) ∧
    (∀ d : ℕ, ∃ (a : ℝ) (T : ℕ), 0 < a ∧
      ∀ N k : ℕ, k ≤ N → T ≤ min k (N-k) →
        BestOverlap d (UniversalLaw N k) ≤ Real.exp (-a * min k (N-k))) ∧
    (∀ N k d : ℕ → ℕ, (∀ j, k j ≤ N j) →
      Asymptotics.IsLittleO Filter.atTop (fun j => (2 : ℝ)^(d j))
        (fun j => ScaleH (N j) (k j)) →
      Filter.Tendsto (fun j => BestOverlap (d j) (UniversalLaw (N j) (k j)))
        Filter.atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (a T : ℝ), 0 < a ∧ 0 < T ∧
      ∀ N k d : ℕ, k ≤ N → T ≤ ScaleH N k →
        (2 : ℝ)^d ≤ (ScaleH N k)^(1-ε) →
        BestOverlap d (UniversalLaw N k) ≤ (2 : ℝ)^(-a * (ScaleH N k)^ε)) ∧
    (∃ (a T : ℝ), 0 < a ∧ 0 < T ∧ ∀ N k d : ℕ, k ≤ N →
      T ≤ ScaleH N k → 1 ≤ d → d ≤ Cutoff N k →
      BestOverlap d (UniversalLaw N k) ≤
        (2 : ℝ)^(-a * min ((k : ℝ)/(2 : ℝ)^d) ((N-k : ℕ)/(4 : ℝ)^d) /
          LogTwo (ScaleH N k))) ∧
    (∀ N k d : ℕ, k ≤ N → (2 : ℝ)^16 ≤ ScaleH N k →
      (k : ℝ) ≤ Real.sqrt (N-k : ℕ) → 1 ≤ d → d ≤ Cutoff N k →
      BestOverlap d (UniversalLaw N k) ≤ (2 : ℝ)^(-(k : ℝ)/(256*(2 : ℝ)^d))) := by sorry

end PolynomialSampling137.OneThird.Supplement

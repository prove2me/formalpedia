-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_Supplement_theorem_3_1
-- name    : PrivateAgnosticHalfspace.Gaussian.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:08:21.652614+00:00
-- url     : https://prove2.me/theorems/f8ed3340-1ca1-4d1d-bf07-d0a159333651
-- title:
--   Theorem 3.1 — private proper Gaussian agnostic learning
-- statement:
--   Let $\alpha,\beta,\delta\in(0,1/2)$ and $\varepsilon\in(0,1)$. There are universal constants $C_0,c,C_{\rm dim},A,B>0$, a natural exponent $r$ and a single costed program, chosen before every dimension, parameter and population. Set $p=\lceil C_0/(c\alpha)^2\rceil$, $D_p=\binom{d+p}{p}$ and suppose $d\ge C_{\rm dim}\alpha^{-5}$. For every labeled distribution $P$ with marginal $N(0,I_d)$, Algorithm 2 is $(\varepsilon,\delta)$-DP on all deterministic neighboring datasets, returns an affine halfspace, and satisfies
--   $$\Pr\{\operatorname{err}_P(h)\le\operatorname{OPT}+\alpha\}\ge1-\beta.$$
--   Its public sample schedule exists and satisfies
--   $$n\le A\left(\frac{D_p}{\alpha^2}+\frac{D_p}{\varepsilon\alpha}+\alpha^{-6}+\frac1{\varepsilon\alpha^5}\right)\Lambda^r,\qquad \Lambda=1+\log\frac1\alpha+\log\frac1\beta+\log\frac1\varepsilon+\log\frac1\delta.$$
--   On every deterministic sample and tape, the same program realizes the learner law and halts using at most $A(n+1)^r\exp(B\alpha^{-4}\log(1/\alpha))$ charged operations. The finite cover is nonempty and its size is at most the public bound used by validation.
--
--   This is the proper agnostic companion theorem: it has coefficient one on both OPT and the additive accuracy, and does not replace the private polynomial estimator by Algorithm 1's L1 regression.
--
--   **Formalization Note** The paper writes soft-O; its proof on pp.33–34 yields the universal constants and fixed logarithm power above, without numerical values. The sample is the least even $n\ge2$ satisfying (31) and $2\sqrt{\log(8K_H/\beta)/n}+4\log(4K_H/\beta)/(\varepsilon n)\le c\alpha$. The dimension constant is at least $2(C_0+1)^2c^{-5}$. No clipping, privacy, excess-loss or cover-success premise is imposed on the unknown population.
--
--   Differences from the source:
--   - encoding: Euclidean examples with labels ±1, affine thresholds, and positive integer dimension → EuclideanSpace over Fin d with d ≥ 1, Borel measures, Bool labels decoded as ±1, sign(0)=+1; reason: coordinate and label encodings preserve all source instances; all real affine thresholds remain allowed
--   - encoding: an explicit sphere net in the spectral subspace and the set H(q) → coordinate Gram–Schmidt of the spectral projection, a normalized rational grid and duplicate-free enumeration of halfspace pairs; reason: fixes a public measurable net construction; it is a c alpha net of the same subspace and has the same exponential cardinality order, including rank zero and the two tails
--   - encoding: soft-O sample count and sufficiently large public constants in (31) and validation → least even feasible count, a deterministic cover upper bound, and uniform A,r with logarithm envelope Lambda; reason: the proof supplies uniform constants; the schedule is independent of random cover size and retains all four terms
--   - reading: arithmetic runtime with symmetric eigendecomposition on p.34 and inverse normal CDF and trigonometric operations in Algorithm 3 → the published sampling real RAM extended by unit-cost sin, cos, pi and normal quantile, and a symmetric spectral projection charged 1+d³; reason: these source operations require explicit semantics and costs; they are not silently expressible in the base scalar alphabet
--   - generalization: the theorem statement on p.7 (no claim about the size of H(q) for an arbitrary coefficient vector) → additional conclusions: the schedule n satisfies its defining condition, and for every coefficient vector in the unit ball the explicit cover is nonempty with at most K_H members; reason: Lemma 3.2 and the trace and covering bounds on pp.31–32 give these facts; dropping the extra conjuncts gives exactly the printed theorem
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), p.7, Theorem 3.1; Algorithm 2 p.9; Eqs. (31) and validation pp.33–34

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Proper

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

/-- Theorem 3.1 (pp.7,33--34): the actual proper learner, unconditional replacement
privacy, exact agnostic error and confidence, all four sample terms, and charged runtime.
Universal constants, logarithm exponent and program precede all learning instances. -/
theorem theorem_3_1 :
    ∃ (c : ProperConstants) (code : Code) (A B : ℝ) (r : ℕ),
      1 ≤ c.degree ∧ 0 < c.accuracy ∧ c.accuracy ≤ 1 / 4 ∧
      2 * (c.degree + 1) ^ 2 * c.accuracy⁻¹ ^ 5 ≤ c.dimension ∧
      0 < c.meanSample ∧ 0 < c.cover ∧ 0 < c.tail ∧ 0 < A ∧ 0 < B ∧
      ∀ d : ℕ, 1 ≤ d → ∀ α β ε δ : ℝ,
      0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
      0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
      c.dimension * α⁻¹ ^ 5 ≤ d →
      let p := properDegree c α
      let n := properSize c d α β ε δ
      let budget := ⌊A * (n + 1 : ℝ) ^ r * Real.exp (B * α⁻¹ ^ 4 * Real.log (1 / α))⌋₊
      properCondition c d α β ε δ n ∧
      (n : ℝ) ≤ A * properSampleScale d p α ε * logs α β ε δ ^ r ∧
      (∀ v : Coeff d p, ‖v‖ ≤ 1 →
        0 < (properCandidates c α v).length ∧
        (properCandidates c α v).length ≤ coverBound c α) ∧
      ∃ L : PrivateUniformGen.Characterization.Mechanism (Example d) (Halfspace d) n,
        Realizes (properLaw c d α ε δ) L ∧
        PrivateUniformGen.Characterization.IsDP L ε δ ∧
        (∀ S : Fin n → Example d,
          ImplementsHalfspace code (budget + 1) budget d
            (properInput c d α β ε δ (List.ofFn S)) (L S : Measure (Halfspace d))) ∧
        ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = gaussian d →
          Accurate L classifier P (opt d P + α) β := by sorry

end PrivateAgnosticHalfspace.Gaussian.Supplement

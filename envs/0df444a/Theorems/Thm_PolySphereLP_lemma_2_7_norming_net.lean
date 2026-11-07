-- Prove2me | Theorems.Thm_PolySphereLP_lemma_2_7_norming_net
-- name    : PolySphereLP.lemma_2_7_norming_net
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:31.783723+00:00
-- url     : https://prove2.me/theorems/4e64879e-876a-4065-9165-ec57dd17f93f
-- title:
--   Lemma 2.7 — coefficient-sphere concentration and a norming net
-- statement:
--   Let $\nu$ be the uniform probability measure on $S^{h-1}$.
--   1. For every $v\in\mathbb R^h$ and $t\in\mathbb R$,
--   $$\mathbb E_{\mathbf a\sim\nu}\big[\exp(t\sqrt h\,\langle\mathbf a,v\rangle)\big]\le\exp(t^2\|v\|^2/2). \tag{37}$$
--   2. Let $n\ge3$, $d\ge2$ even, $h=h_{n,d}$ and $P_{\mathbf a}$ the random harmonic polynomial of (14) for any orthonormal basis. For every $0<\epsilon<1$,
--   $$\mathbb P_{\mathbf a\sim\nu}\Big[\|P_{\mathbf a}\|_\infty>2\sqrt{2\big(n\log(1+8d)+\log(2/\epsilon)\big)}\Big]\le\epsilon. \tag{38}$$
--   3. In particular, for fixed $d$, there is $C_d<\infty$ such that $\|P_{\mathbf a}\|_\infty\le C_d\sqrt n$ with probability at least $1-e^{-n}$.
--
--   This is the standard upper bound on the true optimum, used to divide the LP value in the main theorem.
--
--   **Formalization Note** Clause 1 holds for every dimension $h$. Probability bounds are in inner-measure form: a measurable good event of probability at least $1-\epsilon$ (resp. $1-e^{-n}$). In clause 3, $C_d$ is chosen before $n$ and the basis.
--
--   Differences from the source:
--   - generalization: v ∈ ℝ^h with h = h_{n,d} → every dimension h; reason: the proof uses only the uniform measure on S^{h−1}; h = h_{n,d} is included
--   - encoding: E_{a∼ν}[exp(…)] → lower Lebesgue integral in [0,∞]; reason: the integrand is positive; same value
--   - encoding: P[‖P_a‖_∞ > t] ≤ ε; with probability at least 1 − e^{−n} → a measurable event E with ν(E) ≥ 1 − ε (resp. 1 − e^{−n}) on which ‖P_a‖_∞ ≤ t (resp. ≤ C_d√n) for a ∈ S^{h−1}; reason: equivalent to the outer measure of the bad event being at most ε
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 2.7, p.15, eqs. (37)–(38)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_IsHarmonicONB
import Definitions.Def_PolySphereLP_Pa
import Definitions.Def_PolySphereLP_supNorm
open MeasureTheory

namespace PolySphereLP

/-- **Lemma 2.7 (Coefficient-sphere concentration and a norming net).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 2.7, p.15,
eqs. (37)–(38).

1. (37) For every `v ∈ ℝ^h` and `t ∈ ℝ`, `E_{a∼ν} exp(t√h ⟨a,v⟩) ≤ exp(t²‖v‖²/2)`.
2. (38) For every `0 < ε < 1`, `P_{a∼ν}[‖P_a‖_∞ > 2√(2(n log(1+8d) + log(2/ε)))] ≤ ε`.
3. For fixed `d` there is `C_d < ∞` such that `‖P_a‖_∞ ≤ C_d √n` with probability at least `1 − e^{−n}`.

**Formalization Note.** Clause 1 is stated for every `h` (the paper's `h = h_{n,d}`), with the
expectation as a lower Lebesgue integral. Clauses 2–3 use the model (14) for any orthonormal basis
`Y`, under the standing assumptions `n ≥ 3`, `d ≥ 2` even (p.9), with probability bounds in the
inner-measure form (a measurable good event of mass `≥ 1 − ε`, resp. `≥ 1 − e^{−n}`, equivalent to the
outer measure of the bad event being `≤ ε`). In clause 3, `C_d` is chosen before `n` and `Y`. -/
theorem lemma_2_7_norming_net :
    (∀ (h : ℕ) (v : Fin h → ℝ) (t : ℝ),
      ∫⁻ a, ENNReal.ofReal (Real.exp (t * Real.sqrt h * ∑ i, a i * v i)) ∂(SphereSOS.Rate.sigma h) ≤
        ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i, v i ^ 2) / 2))) ∧
    (∀ n d : ℕ, 3 ≤ n → 2 ≤ d → Even d → ∀ (h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ),
      IsHarmonicONB n d h Y → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ E : Set (Fin h → ℝ), MeasurableSet E ∧
        ENNReal.ofReal (1 - ε) ≤ SphereSOS.Rate.sigma h E ∧
        ∀ a ∈ E, a ∈ SphereSOS.Rate.sphere h →
          supNorm n (Pa Y a) ≤
            2 * Real.sqrt (2 * ((n : ℝ) * Real.log (1 + 8 * (d : ℝ)) + Real.log (2 / ε)))) ∧
    (∀ d : ℕ, 2 ≤ d → Even d → ∃ Cd : ℝ, ∀ n : ℕ, 3 ≤ n →
      ∀ (h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ), IsHarmonicONB n d h Y →
      ∃ E : Set (Fin h → ℝ), MeasurableSet E ∧
        ENNReal.ofReal (1 - Real.exp (-(n : ℝ))) ≤ SphereSOS.Rate.sigma h E ∧
        ∀ a ∈ E, a ∈ SphereSOS.Rate.sphere h → supNorm n (Pa Y a) ≤ Cd * Real.sqrt n) := by sorry

end PolySphereLP

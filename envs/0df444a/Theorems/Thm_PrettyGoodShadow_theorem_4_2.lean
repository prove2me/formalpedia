-- Prove2me | Theorems.Thm_PrettyGoodShadow_theorem_4_2
-- name    : PrettyGoodShadow.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:32.8682+00:00
-- url     : https://prove2.me/theorems/489d94df-9990-419a-be2c-85430c808987
-- title:
--   Theorem 4.2 — the boosted integral PGM solves average-case shadow tomography with $O(\log(2m)\log(2m/\delta)/\varepsilon^2)$ copies (corrected: $\log m\to\log 2m$)
-- statement:
--   There is an absolute constant $C>0$ with the following properties. Let $\{\rho_x\}_{x\in\mathcal L}$ be a finite family of $d$-dimensional states, $p$ a prior, $O_1,\dots,O_m$ Hermitian with $\|O_i\|_\infty\le1$, $m\ge1$, and $\varepsilon,\delta>0$.
--
--   1. **(A) The algorithm succeeds.** For all admissible $k,T,R$, the boosted integral pretty good measurement of Appendix A satisfies
--
--   $$
--   \Pr\Big[\max_{i\in[m]}|\hat o_i-\operatorname{tr}(O_i\rho)|>\varepsilon\Big]\le\delta.
--   $$
--
--   2. **(B) Copies.** If $\varepsilon\le2$ and $\delta<1$, there are admissible $k,T,R$, depending only on $m,\varepsilon,\delta$, with
--
--   $$
--   R\cdot k(2T-1)\le C\,\frac{\log(2m)\log(2m/\delta)}{\varepsilon^2}.
--   $$
--
--   3. **(C) The printed statement.** For every integer $n\ge C\log(2m)\log(m/\delta)/\varepsilon^2$ there are a finite-outcome POVM $\{N_z\}$ on $n$ copies and a decoder $g$, both chosen before $x$, with
--
--   $$
--   \Pr_{x\sim p,\,z}\Big[\max_{i\in[m]}|g_i(z)-\operatorname{tr}(O_i\rho_x)|\le\varepsilon\Big]\ge1-\delta.
--   $$
--
--   Here the admissible parameters are those with $k\ge48/\varepsilon^2$, $T\ge1$, $2me^{-T/128}\le1/8$, $R$ odd and $m(\sqrt3/2)^R\le\delta$. The theorem is the average-case result from which the source derives its worst-case bound through the minimax theorem.
--
--   **Formalization Note** The constant $C$ is chosen before all data, and (B) precedes the instance, so $k,T,R$ cannot depend on it. Zero prior weights are allowed. Natural logarithm. The worst-case Theorem 1.1 is posed elsewhere on the platform as `DimFreeShadow.theorem_1_2`. The case $m=1$, $\delta\in(1/2,1)$ of (C) is not reached by the source's algorithm, which always uses copies; it still holds, by a Chebyshev estimate combined with a uniform guess on a grid of spacing $2\varepsilon$.
--
--   Differences from the source:
--   - correction: O(log(m) log(m/δ)/ε²) copies → C log(2m) log(m/δ)/ε² in (C), C log(2m) log(2m/δ)/ε² in (B); reason: the printed rate is 0 at m = 1, which is false. Counterexample: m = 1, O = Z, ρ₀ = |0⟩⟨0|, ρ₁ = |1⟩⟨1|, uniform p, ε = 1/2, δ = 1/4: with 0 copies the output law does not depend on x, so the average success is at most 1/2 < 3/4. For m ≥ 2 and δ < 1 the rates agree up to a factor 2
--   - generalization: there is an algorithm → the named boosted algorithm succeeds for all admissible parameters (A), with an explicit copy count (B), together with the existential form (C); reason: (C) is the printed claim and is implied in the range ε ≤ 2, δ < 1, m ≥ 2 by (A) and (B) with unused copies ignored
--   - encoding: O(·) → one constant C before the instance; n ≥ bound in (C); reason: this is the meaning of O(·) with an absolute constant; unused copies are ignored
--   - encoding: for any δ, ε > 0 → (B) has log(2m/δ) and is restricted to ε ≤ 2, δ < 1; reason: the algorithm always uses at least one copy while the rate tends to 0 as ε → ∞ and is at most 0 for large δ; (C) has no such restriction and covers every δ, ε > 0
--   - reading: Lemma 4.3 and Appendix A use k = ⌈12/ε²⌉ with ∥O_i∥∞ ≤ 1 → admissible parameters have k ≥ 48/ε²; reason: the source normalizes to 0 ⪯ O ⪯ I at accuracy ε/2 (§4.1, p.19), which gives this threshold; Theorem 4.2 prints no k, and k enters only through O(·)
--   - encoding: observables O_1, …, O_m and the rate log(m) → hypothesis 1 ≤ m; reason: log(m) is undefined at m = 0, and with no observables the success event is empty of constraints, so m = 0 is only the degenerate case of the problem
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Theorem 4.2, p.18 (= Theorem 1.2, p.4); proof in Appendix A, pp.31–32

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_PrettyGoodShadow_failureProb

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Theorem 4.2 (= Theorem 1.2), about the paper's algorithm, with `log m` corrected to `log(2m)`** (arXiv:2610.06781,
sha256 bd055b7d…, Theorem 4.2, p.18, Theorem 1.2, p.4; proof in Appendix A, pp.31–32). There is an absolute constant
`C > 0` such that, for any finite family of `d`-dimensional states, any prior, any observables `O_1, …, O_m` with
`‖O_i‖_∞ ≤ 1` and any `ε, δ > 0`:

* (A) the boosted integral PGM of Appendix A has failure probability at most `δ` for all admissible `k, T, R`;
* (B) if `ε ≤ 2` and `δ < 1`, then admissible `k, T, R` exist, depending on `m, ε, δ` only, with
  `R · k(2T − 1) ≤ C log(2m) log(2m/δ)/ε²` copies;
* (C) the printed statement: for every `n ≥ C log(2m) log(m/δ)/ε²` there is one finite-outcome POVM on `n` copies with a
  decoder `g`, both chosen before `x`, that solves Problem 4.1.

**Formalization Note** `C` is chosen before all data, and (B) is stated before the instance, so `k, T, R` cannot depend on
it. Zero prior weights are allowed. Natural logarithm. The norm is the `L²` operator norm. In (C), `n` may exceed the
bound, since unused copies are ignored, and `n` may be `0`, in which case the POVM acts on a one-point space. -/
theorem theorem_4_2 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (m : ℕ) (ε δ : ℝ), 1 ≤ m → 0 < ε → ε ≤ 2 → 0 < δ → δ < 1 →
        ∃ k T R : ℕ, Admissible m ε δ k T R ∧
          ((R * (k * (2 * T - 1)) : ℕ) : ℝ) ≤
            C * Real.log (2 * (m : ℝ)) * Real.log (2 * (m : ℝ) / δ) / ε ^ 2) ∧
      (∀ {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ),
        (∀ x, WildeQIT.IsDensityOperator (ρ x)) →
        ∀ p : L → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
        ∀ (m : ℕ), 1 ≤ m → ∀ O : Fin m → Matrix d d ℂ, (∀ i, (O i).IsHermitian) →
        (∀ i, ‖O i‖ ≤ 1) → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
          (∀ k T R : ℕ, Admissible m ε δ k T R → failureProb p ρ O ε k T R ≤ δ) ∧
          (∀ n : ℕ, C * Real.log (2 * (m : ℝ)) * Real.log ((m : ℝ) / δ) / ε ^ 2 ≤ (n : ℝ) →
            ∃ (Z : Type) (_ : Fintype Z) (N : Z → Matrix (Fin n → d) (Fin n → d) ℂ)
              (g : Z → Fin m → ℝ), QAlgorithms.IsPOVM N ∧
              1 - δ ≤ ∑ x, p x * ∑ z with (∀ i, |g z i - obs (O i) (ρ x)| ≤ ε),
                (N z * tensorPow (ρ x) n).trace.re)) := by sorry

end PrettyGoodShadow

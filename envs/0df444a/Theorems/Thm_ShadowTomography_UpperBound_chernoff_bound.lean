-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_chernoff_bound
-- name    : ShadowTomography.UpperBound.chernoff_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:43.804984+00:00
-- url     : https://prove2.me/theorems/3404c8ec-e326-4998-9ffd-67351108921c
-- title:
--   Proof of Theorem 2, p. 18 — 1 − Tr(F_tρ*) ≤ ε⁴/log² D when Tr(E_jρ) ≥ Tr(E_jρ_t) + ε/2
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $E$ be a two-outcome measurement and $\rho$ a mixed state of any finite dimension, let $D\ge2$, $0<\varepsilon\le1/2$, $a\in\mathbb R$ (in the paper $a=\mathrm{Tr}(E_j\rho_t)$), and let $q$ satisfy
--
--   $$
--   q \ge \frac{C}{\varepsilon^2}\Big(\log\log D + \log\frac1\varepsilon\Big).
--   $$
--
--   Let $F$ apply $E$ to each of the $q$ copies in $\rho^{\otimes q}$ and accept iff at least $(a+\varepsilon/4)q$ invocations accept. If $\mathrm{Tr}(E\rho)\ge a+\varepsilon/2$, then
--
--   $$
--   1-\mathrm{Tr}(F\rho^{\otimes q}) \le \frac{\varepsilon^4}{\log^2 D}.
--   $$
--
--   In the proof of Theorem 2 this is the per-iteration rejection probability of the true amplified state, which Lemma 12 then sums over all iterations.
--
--   **Formalization Note** $D$ enters only as a parameter of the bound and is not tied to the dimension of $\rho$. $D\ge2$ is required: at $D=1$, $\log D=0$ and the right side is $\varepsilon^4/0=0$ in Lean. $\varepsilon\le1/2$ is the regime of Theorem 2 and keeps $\log\log D+\log(1/\varepsilon)>0$. The page writes the hypothesis as "the expected number of accepting invocations is at least $(\mathrm{Tr}(E_i\rho_t)+\varepsilon/2)q$", with $E_i$ a typo for $E_j$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, pp. 17–18, proof of Theorem 2 (display 1 − Tr(F_tρ^*) ≤ ε^4/log^2 D, p. 18)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Proof of Theorem 2, p. 18 (Chernoff claim).** There is a universal constant `C` such that
for `D ≥ 2`, `0 < ε ≤ 1/2` and `q ≥ (C/ε²)(log log D + log(1/ε))`: if `Tr(Eρ) ≥ a + ε/2`, the
measurement accepting iff at least `(a + ε/4) q` of the `q` invocations of `E` accept rejects
`ρ^{⊗q}` with probability at most `ε⁴ / log² D`. Here `a` stands for `Tr(E_j ρ_t)`. -/
theorem chernoff_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (E ρ : Matrix n n ℂ) (D : ℕ) (a ε : ℝ) (q : ℕ),
        IsEffect E → WildeQIT.IsDensityOperator ρ → 2 ≤ D → 0 < ε → ε ≤ 1 / 2 →
        C / ε ^ 2 * (Real.log (Real.log D) + Real.log (1 / ε)) ≤ (q : ℝ) →
        a + ε / 2 ≤ (E * ρ).trace.re →
        1 - (ampAtLeast E q (a + ε / 4) * tensorPow ρ q).trace.re ≤ ε ^ 4 / Real.log D ^ 2 := by sorry

end ShadowTomography.UpperBound

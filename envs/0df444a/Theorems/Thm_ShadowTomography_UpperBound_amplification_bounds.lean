-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_amplification_bounds
-- name    : ShadowTomography.UpperBound.amplification_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:33.331223+00:00
-- url     : https://prove2.me/theorems/2f6871f1-c1e3-4e7f-829c-eb547f9b0599
-- title:
--   Proof of Theorem 2, p. 16 — amplified tests E*_{i,t,±} accept w.p. ≥ 5/6 when off by ε, ≤ 1/3 when within ε/2
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $E$ be a two-outcome measurement and $\rho$ a mixed state of any finite dimension, let $a\in\mathbb R$ (in the paper, $a=\mathrm{Tr}(E\rho_t)$ for the current hypothesis $\rho_t$), $\varepsilon>0$ and $q\ge C/\varepsilon^2$. Let $E^*_{+}$ apply $E$ to each of the $q$ copies in $\rho^{\otimes q}$ and accept iff at least $(a+3\varepsilon/4)q$ invocations accept, and $E^*_{-}$ accept iff at most $(a-3\varepsilon/4)q$ invocations accept. Then:
--
--   1. if $\mathrm{Tr}(E\rho)\ge a+\varepsilon$, then $\mathrm{Tr}(E^*_{+}\rho^{\otimes q})\ge 5/6$;
--   2. if $\mathrm{Tr}(E\rho)\le a-\varepsilon$, then $\mathrm{Tr}(E^*_{-}\rho^{\otimes q})\ge 5/6$;
--   3. if $|\mathrm{Tr}(E\rho)-a|\le\varepsilon/2$, then
--   $$
--   \mathrm{Tr}(E^*_{+}\rho^{\otimes q})\le\tfrac13 \quad\text{and}\quad \mathrm{Tr}(E^*_{-}\rho^{\otimes q})\le\tfrac13 .
--   $$
--
--   These are the separation properties that let Gentle Search, run on the amplified state $\rho^{\otimes q}$, find a measurement on which the hypothesis is off by about $\varepsilon$.
--
--   **Formalization Note** The hypothesis $\rho_t$ enters only through the number $a=\mathrm{Tr}(E\rho_t)$, so $a$ is a free real parameter. The paper's $q:=\frac{C}{\varepsilon^2}(\log\log D+\log\frac1\varepsilon)$ is replaced by the weaker requirement $q\ge C/\varepsilon^2$, which the page states is all this claim needs. The amplified tests are `ampAtLeast`/`ampAtMost` with real thresholds.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 16, proof of Theorem 2 (paragraphs defining E^*_{i,t,±} and the two Chernoff claims)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Proof of Theorem 2, p. 16 (amplification claims).** There is a universal constant `C` such
that, whenever `q ≥ C/ε²`, the amplified measurements `E^*_{+}` (accept iff at least
`(a + 3ε/4) q` of the `q` invocations of `E` accept) and `E^*_{-}` (accept iff at most
`(a - 3ε/4) q` accept) satisfy on `ρ^{⊗q}`: `Tr(E^*_{+} ρ^{⊗q}) ≥ 5/6` if `Tr(Eρ) ≥ a + ε`;
`Tr(E^*_{-} ρ^{⊗q}) ≥ 5/6` if `Tr(Eρ) ≤ a - ε`; and both are at most `1/3` if
`|Tr(Eρ) - a| ≤ ε/2`. Here `a` stands for `Tr(E ρ_t)`. -/
theorem amplification_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (E ρ : Matrix n n ℂ) (a ε : ℝ) (q : ℕ),
        IsEffect E → WildeQIT.IsDensityOperator ρ → 0 < ε → C / ε ^ 2 ≤ (q : ℝ) →
        (a + ε ≤ (E * ρ).trace.re →
            5 / 6 ≤ (ampAtLeast E q (a + 3 * ε / 4) * tensorPow ρ q).trace.re) ∧
        ((E * ρ).trace.re ≤ a - ε →
            5 / 6 ≤ (ampAtMost E q (a - 3 * ε / 4) * tensorPow ρ q).trace.re) ∧
        (|(E * ρ).trace.re - a| ≤ ε / 2 →
            (ampAtLeast E q (a + 3 * ε / 4) * tensorPow ρ q).trace.re ≤ 1 / 3 ∧
            (ampAtMost E q (a - 3 * ε / 4) * tensorPow ρ q).trace.re ≤ 1 / 3) := by sorry

end ShadowTomography.UpperBound

-- Prove2me | Theorems.Thm_QMCBeyondHK_density_integral_eq_one
-- name    : QMCBeyondHK.density_integral_eq_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:13.546314+00:00
-- url     : https://prove2.me/theorems/c3887da6-397e-4b58-ba8e-2878d3ab19a9
-- title:
--   §3.1 — $\int\mu_t = 1$: Haar-thinning is a $(1+\varepsilon)$-online thinning strategy
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$ and $\ell = \lceil 10\log_2 n\rceil$.
--
--   1. For every list $A$ of retained points, the Haar-thinning density (7) satisfies
--   $$
--   \int_{[0,1)^d} \mu(x)\,dx = 1,
--   $$
--   because every non-constant Haar function has mean zero.
--   2. Consequently, along the run of the strategy on any input stream $(x_t,\xi_t,y_t)$, the densities $\mu_t$ built from $A_t$ form a target-density rule of the $(1+\varepsilon)$-online thinning framework: they lie in $[1-\varepsilon/2, 1+\varepsilon/2]$ on the cube, integrate to one, and are determined by the randomness of the steps before $t$.
--
--   So the results proved for the general framework (Fact 2.3, Proposition 2.4) apply to Haar-thinning.
--
--   Differences from the source:
--   - generalization: μ_t at step t of a run of the strategy → the density (7) built from an arbitrary list A of points (first clause); reason: the integral is one for every value of the discrepancies; the retained list of any run is such a list
--   - encoding: μ_t satisfies the requirement of the (1 + ε)-thinning framework → IsThinningDensity: range, integral one, joint measurability in the randomness of the earlier steps, for every input stream; reason: the framework's requirement, written out
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §3.1, p.9 (PDF p.11): 'Moreover, ∫ µ_t = 1 … Thus µ_t is a probability density satisfying the requirement of the (1 + ε)-thinning framework in Section 2.1.'

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_IsThinningDensity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- §3.1, printed p.9 (PDF p.11) of arXiv:2609.10921 (sha256 bc273e88…): `∫ μ_t = 1`, as every
non-constant Haar function has mean zero; thus `μ_t` is a probability density satisfying the
requirement of the `(1 + ε)`-thinning framework of §2.1.

**Formalization Note** The second conjunct says that the Haar-thinning densities along the run,
on any input stream, form a target-density rule of the framework (`IsThinningDensity`: range,
integral one, and determined by the randomness of the earlier steps). -/
theorem density_integral_eq_one (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ A : List (Fin d → ℝ), ∫ x in cube d, density d ε (ell n) A x = 1) ∧
    (∀ {Ω : Type*} (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
      IsThinningDensity ε X Ξ Y
        (fun t ω x => density d ε (ell n) (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) x)) := by sorry

end QMCBeyondHK

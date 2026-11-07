-- Prove2me | Theorems.Thm_QMCBeyondHK_theorem_2_2
-- name    : QMCBeyondHK.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:08.724201+00:00
-- url     : https://prove2.me/theorems/72939b90-84d9-4d45-8751-4b88574f4e48
-- title:
--   Theorem 2.2 ([CJJ26]) — $\mathbb E_s\|f_s\|_B^2 = \Theta_d(\sigma_{SO}(f)^2)$ (corrected: mean-zero $f$ for the upper bound)
-- statement:
--   Let $d \ge 1$. There are constants $0 < c_d$ and $0 < C_d$, depending only on $d$, such that for every $f \in L^2([0,1)^d)$:
--
--   1. $\displaystyle c_d\, \sigma_{SO}(f)^2 \le \mathbb E_{s \sim \mathrm{Unif}[0,1)^d}\big[\|f_s\|_B^2\big]$;
--   2. if $\bar f = 0$, then $\displaystyle \mathbb E_{s \sim \mathrm{Unif}[0,1)^d}\big[\|f_s\|_B^2\big] \le C_d\, \sigma_{SO}(f)^2$.
--
--   Here $f_s(x) = f(x + s \bmod [0,1)^d)$. The shift-averaged Haar–Besov seminorm is thus equivalent to the smoothed-out variation; this is the black box that turns the Haar-basis error bound of the mission into the $\sigma_{SO}$ bound of Theorem 1.2.
--
--   Differences from the source:
--   - correction: E_s[‖f_s‖²_B] = Θ_d(σ_SO(f)²) for every f ∈ L² → the lower bound for every f, the upper bound only when ∫f = 0; reason: counterexample: f ≡ 1 has σ_SO(f) = 0 but ‖f_s‖²_B ≥ ⟨1, H_{0,0}⟩²/‖H_{0,0}‖₂⁴ = 1 for every s (proved in the sanity file); §3.3 applies the theorem only after reducing to f̄ = 0
--   - reading: Definition 2.1's index range 0 ≤ k_i < 2^{j_i} → §2's range: k_i < 2^{j_i − 1} for j_i ≥ 1, k_i = 0 for j_i = 0; reason: the extra indices name no Haar function of §2
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: Θ_d(·), E_s, ‖·‖²_B, σ_SO(f)² as real quantities → ∃ c_d, C_d > 0 chosen after d; E_s a lower Lebesgue integral over the cube; seminorms in ℝ≥0∞; reason: Θ_d means two-sided bounds with constants depending on d only; nonnegative quantities in ℝ≥0∞ have no junk value
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Theorem 2.2, p.6 (PDF p.8) (cited from [CJJ26]); used in §3.3, pp.12–13 (PDF pp.14–15) after 'we may assume that f̄ = 0'

import Mathlib
import Definitions.Def_QMCBeyondHK_besovSq
import Definitions.Def_QMCBeyondHK_sigmaSOSq

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Theorem 2.2 (Shift-averaged seminorm equivalence, cited from [CJJ26]), printed p.6 (PDF p.8)
of arXiv:2609.10921 (sha256 bc273e88…), **corrected**: for any `f ∈ L²([0,1)^d)`,
`E_{s∼[0,1)^d}[‖f_s‖²_B] = Θ_d(σ_SO(f)²)` — the lower bound for every `f`, the upper bound for `f`
with mean zero.

**Formalization Note** As printed the upper bound fails for nonzero constants: `f ≡ 1` has
`σ_SO(f) = 0` but `‖f_s‖²_B ≥ ⟨1, H_{0,0}⟩²/‖H_{0,0}‖₂⁴ = 1` for every `s`. The proof of Theorem 1.2
(§3.3, p.12) applies it after reducing to `f̄ = 0`. The constants depend on `d` only; `E_s` is the
integral over `s ∈ [0,1)^d`; both sides are in `ℝ≥0∞`. -/
theorem theorem_2_2 (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : (Fin d → ℝ) → ℝ, Measurable f → MemLp f 2 (unif d) →
      ENNReal.ofReal c * sigmaSOSq d f ≤ ∫⁻ s in cube d, besovSq d (shiftFun f s) ∧
      (cubeMean d f = 0 → ∫⁻ s in cube d, besovSq d (shiftFun f s) ≤ ENNReal.ofReal C * sigmaSOSq d f) := by sorry

end QMCBeyondHK

-- Prove2me | Theorems.Thm_TalagrandCore_kr_prop21
-- name    : TalagrandCore.kr_prop21
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:34.888504+00:00
-- url     : https://prove2.me/theorems/c730bc82-ddc8-4005-866a-14f6656be075
-- title:
--   Klein–Rio Proposition 2.1 on a finite Bernoulli cube
-- statement:
--   Let $f>0$ be a function on a finite product space and let $g_x>0$ be auxiliary functions. Writing $E_x$ for expectation over coordinate $x$, generalized entropy tensorization gives
--
--   $$
--   \operatorname{Ent}(f)\le
--   \sum_x\left(\mathbb E\left[g_x\log\frac{g_x}{E_xg_x}\right]
--   +\mathbb E\left[(f-g_x)\log\frac{f}{E_xf}\right]\right).
--   $$
--
--   This is Proposition 2.1 of Klein–Rio specialized to the finite Bernoulli product space.
--
--   **Formalization Note** Positivity hypotheses replace the integrability side conditions, which are automatic on the finite cube.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem kr_prop21 (p : NNReal) (hp : p ≤ 1)
    (f : (κ → Bool) → ℝ) (hf : ∀ ω, 0 < f ω)
    (g : κ → (κ → Bool) → ℝ) (hg : ∀ x ω, 0 < g x ω) :
    Ex (p : ℝ) (fun ω => f ω * Real.log (f ω)) -
      Ex (p : ℝ) f * Real.log (Ex (p : ℝ) f) ≤
      ∑ x : κ,
        (Ex (p : ℝ) (fun ω => g x ω * Real.log (g x ω / condEx (p : ℝ) x (g x) ω)) +
          Ex (p : ℝ) (fun ω => (f ω - g x ω) *
            Real.log (f ω / condEx (p : ℝ) x f ω))) := by sorry

end TalagrandCore

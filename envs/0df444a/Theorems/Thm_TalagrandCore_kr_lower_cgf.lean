-- Prove2me | Theorems.Thm_TalagrandCore_kr_lower_cgf
-- name    : TalagrandCore.kr_lower_cgf
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:46.766222+00:00
-- url     : https://prove2.me/theorems/ed021532-207e-4842-8565-09dd40445568
-- title:
--   Klein–Rio lower-tail cumulant bound for a finite linear supremum
-- statement:
--   Let $Z$ be a finite centered Bernoulli linear supremum with coefficient envelope one and variance proxy $\sigma^2$. For $0<t\le1/4$,
--
--   $$
--   \log\mathbb E e^{-tZ}
--   \le -t\,\mathbb EZ+4(\sigma^2+\mathbb EZ)t^2.
--   $$
--
--   This is the integrated compensated-process inequality underlying the lower-tail concentration estimate.
--
--   **Formalization Note** The integration is formalized through a frozen-branch derivative comparison and a right-slope fencing lemma.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem kr_lower_cgf (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1/4) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω)))) ≤
      -(t * Ex (p : ℝ) (Zproc coeff (p : ℝ))) +
        4 * (sigmaSq + Ex (p : ℝ) (Zproc coeff (p : ℝ))) * t ^ 2 := by sorry

end TalagrandCore

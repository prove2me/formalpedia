-- Prove2me | Theorems.Thm_TalagrandCore_contraction_main
-- name    : TalagrandCore.contraction_main
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:13.214547+00:00
-- url     : https://prove2.me/theorems/c6a5f64a-3fb8-4666-b6b9-f00149c2ac5a
-- title:
--   Rademacher contraction from squared to linear coordinate sums
-- statement:
--   For coefficients $u_a(x)$ bounded by one in absolute value, replacing selected signed quadratic terms by twice the corresponding signed linear terms can only increase the expected finite supremum. In particular,
--
--   $$
--   \mathbb E_\varepsilon\max_a\left(\sum_{x\in S}\varepsilon_xu_a(x)^2+
--   \sum_{x\notin S}2\varepsilon_xu_a(x)\right)
--   \le \mathbb E_\varepsilon\max_a\sum_x2\varepsilon_xu_a(x).
--   $$
--
--   This is the induction form of the Rademacher contraction principle needed for the variance-process bound.
--
--   **Formalization Note** Rademacher signs are encoded by Boolean coordinates with parameter $1/2$.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem contraction_main (u : ι → κ → ℝ) (hu : ∀ a x, |u a x| ≤ 1) (S : Finset κ) :
    Ex (1/2 : ℝ) (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
          (∑ x ∈ S, sg (s x) * u a x ^ 2) + ∑ x ∈ Sᶜ, sg (s x) * (2 * u a x))) ≤
      Ex (1/2 : ℝ) (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => ∑ x : κ, sg (s x) * (2 * u a x))) := by sorry

end TalagrandCore

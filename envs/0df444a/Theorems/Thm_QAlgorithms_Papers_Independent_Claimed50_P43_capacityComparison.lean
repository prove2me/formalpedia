-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_capacityComparison
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.capacityComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:23:58.403546+00:00
-- url     : https://prove2.me/theorems/01e62f7f-0e95-41a2-aea5-b6cbc4a43b8e
-- title:
--   Assisted capacity is at most regularized classical capacity plus input log-dimension
-- statement:
--   Let $\Phi:A\to A'$ be a CPTP channel between nonzero finite-dimensional spaces and let $d=\dim A$. Let $C^{(1)}$ denote the unassisted Holevo maximum over finite normalized ensembles. Both ordinary normalized block limits defining $C$ and $C_{\rm ea}$ exist, and for every $n\ge1$,
--
--   $$C_{\rm ea}^{(1)}(\Phi^{\otimes n})\le C^{(1)}(\Phi^{\otimes n})+n\log_2d,\qquad C_{\rm ea}(\Phi)\le C(\Phi)+\log_2d.$$
--
--   Here $C(\Phi)=\lim_{n\to\infty}C^{(1)}(\Phi^{\otimes n})/n$. The dimension term belongs to the input and retained reference. This comparison concerns regularized classical capacity.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 7, §III, unnumbered capacity comparison, with equation (22)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.7, (22) and following limit: regularized unassisted comparison, with
convergence retained. d is the input/reference dimension, not output dimension. -/
theorem capacityComparison {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) :
    Tendsto (classicalRate N) atTop (nhds (regularizedClassicalHolevo N)) ∧
    Tendsto (assistedRate N) atTop (nhds (regularizedAssistedHolevo N)) ∧
    (∀ n : ℕ, 0 < n → assistedOneShot (piSuperop (fun _ : Fin n => N)) ≤
      holevoCapacity (piSuperop (fun _ : Fin n => N)) + n * Real.logb 2 (Fintype.card A)) ∧
    regularizedAssistedHolevo N ≤ regularizedClassicalHolevo N + Real.logb 2 (Fintype.card A) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end

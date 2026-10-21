-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_constrained_holevo_concavity
-- name    : QAlgorithms.Papers.Independent.Support21.P19.constrained_holevo_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:11:59.045984+00:00
-- url     : https://prove2.me/theorems/0d88208b-6fee-4b4c-bcd7-349eea2932f2
-- title:
--   Concavity of the constrained Holevo gain
-- statement:
--   For a finite-dimensional bipartite unitary $U$, let $\Delta\chi_e(U)$ be its extended-real constrained Holevo gain, optimized over all finite pure-state ensembles and arbitrary local ancillas. If $p_j\ge0$, $\sum_jp_j=1$, and $e_j\in\mathbb R$, then
--
--   $$
--   \sum_{j:p_j>0}p_j\Delta\chi_{e_j}(U)\le\Delta\chi_{\sum_jp_je_j}(U).
--   $$
--
--   Terms with weight zero are omitted. A positive weight at an infeasible budget contributes $-\infty$ on the left; at finite feasible values this is the usual Jensen inequality. The optimization permits locally retained flags at both parties, with $U$ acting as identity on the flags. Concavity relates mixtures of per-use budgets to their average.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 4, Concavity of the constrained Holevo gain

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, concavity proof: arbitrary finite mixing, with locally retained shared flags.
Positive weight on an infeasible budget gives a bottom left side. For finite feasible
values this is exactly the usual Jensen inequality; zero weights contribute zero. -/
theorem constrained_holevo_concavity (U : Resource) (hU : IsUnitaryResource U) {l : ℕ}
    (p : Fin l → ℝ) (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i=1) (e : Fin l → ℝ) :
    weightedValue p (fun i => DeltaChi U (e i)) ≤ DeltaChi U (∑ i, p i*e i) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_freeAdmixture
-- name    : QAlgorithms.Papers.Independent.Information100.P04.freeAdmixture
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:36:13.320975+00:00
-- url     : https://prove2.me/theorems/de2f9fcd-93e8-4c12-96ee-ab6fe355aaa8
-- title:
--   PPT free admixture and propagation of Werner bounds
-- statement:
--   Let $\rho$ and $\tau$ be bipartite density matrices on nonzero finite-dimensional systems, and suppose $\tau$ is PPT. For every $s\in[0,1]$,
--
--   $$E_{d,\mathrm{PPT}}(s\rho+(1-s)\tau)\le sE_{d,\mathrm{PPT}}(\rho).$$
--
--   For Werner states of local dimension $d\ge2$, the ratio $E_{d,\mathrm{PPT}}(\rho_p)/(p-1/2)$ is nondecreasing on $(1/2,1]$. For $1/2<p\le q\le1$, $\rho_p=[(p-1/2)/(q-1/2)]\rho_q+[1-(p-1/2)/(q-1/2)]\rho_{1/2}$, and $\rho_{1/2}^\Gamma=(I-\Phi_d)/(d^2-1)$. Thus any upper bound $U\ge E_{d,\mathrm{PPT}}(\rho_q)$ gives $E_{d,\mathrm{PPT}}(\rho_p)\le(p-1/2)U/(q-1/2)$ also at $p=1/2$, while a lower bound $V\le E_{d,\mathrm{PPT}}(\rho_p)$ propagates rightward as $E_{d,\mathrm{PPT}}(\rho_q)\ge(q-1/2)V/(p-1/2)$. These implications preserve valid bounds under pointwise minima or maxima; they make no general convexity or arbitrary interpolation assertion.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 31, eq139-140

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Free-admixture inequality and Werner propagation rule, eqs.(139)–(140), PDF p.31.
Includes s=0,1 and the zero left endpoint; rightward divisions require p>1/2. -/
theorem freeAdmixture {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho tau : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (htau : IsPPT tau) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      distillable ((s:ℂ) • rho + ((1-s:ℝ):ℂ) • tau) ≤ s * distillable rho) ∧
    (∀ d : ℕ, 2 ≤ d →
      (gamma (werner d (1/2)) = (((d:ℂ)^2-1)⁻¹) • (1-bellProjector d)) ∧
      (∀ p q : ℝ, 1/2 < p → p ≤ q → q ≤ 1 →
        distillable (werner d p)/(p-1/2) ≤ distillable (werner d q)/(q-1/2) ∧
        werner d p = (((p-1/2)/(q-1/2):ℝ):ℂ) • werner d q +
          ((1-(p-1/2)/(q-1/2):ℝ):ℂ) • werner d (1/2)) ∧
      (∀ p q U : ℝ, 1/2 ≤ p → p ≤ q → 1/2 < q → q ≤ 1 →
        distillable (werner d q) ≤ U → distillable (werner d p) ≤ (p-1/2)*U/(q-1/2)) ∧
      (∀ p q V : ℝ, 1/2 < p → p ≤ q → q ≤ 1 →
        V ≤ distillable (werner d p) → (q-1/2)*V/(p-1/2) ≤ distillable (werner d q))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end

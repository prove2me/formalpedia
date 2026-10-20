-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_nsEqualsEA
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.nsEqualsEA
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:36:21.11191+00:00
-- url     : https://prove2.me/theorems/00ba4eff-059e-4484-acdd-f6dadfc519f9
-- title:
--   Corollary 7: NS capacity equals EA capacity
-- statement:
--   Let $\mathcal N:A\to B$ be any CPTP channel on nonzero finite registers. Let $\phi_\rho$ purify a density input $\rho$, and write $H$ for von Neumann entropy in bits. Define $I(\rho;\mathcal N)=H(\rho)+H(\mathcal N(\rho))-H((\mathrm{id}\otimes\mathcal N)\phi_\rho)$. The input maximum is attained, and the iterated limits satisfy
--
--   $$\lim_{e\downarrow0}\lim_{n\to\infty}\frac1n C_{\mathrm{NS}}^{(1)}(\mathcal N^{\otimes n},e)\le\max_\rho I(\rho;\mathcal N),\qquad C_{\mathrm{NS}}(\mathcal N)=C_E(\mathcal N).$$
--
--   The Lean statement supplies the inner and outer limits explicitly; the error approaches zero through $(0,1)$. Operational capacities optimize integer-message collective codes with vanishing average error and no feedback. This relates NS assistance to ordinary shared-entanglement assistance asymptotically.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 11, Corollary 7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.11–12, Corollary 7: the iterated limit and the operational capacity
identity. The error limit is taken from 0<e<1; no limit at e=1 is used.
The damaged entropy glyph on p.12 is read as the specified purification. -/
theorem nsEqualsEA [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    IsGreatest {r | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ r = channelMI N rho}
      (maxMI N) ∧
    (∃ g : ℝ → ℝ, ∃ L : ℝ,
      (∀ e : ℝ, 0 < e → e < 1 →
        Tendsto (fun n : ℕ => oneShot false (piSuperop (fun _ : Fin n => N)) e /
          (n : ℝ)) atTop (nhds (g e))) ∧
      Tendsto g (nhdsWithin 0 (Set.Ioo 0 1)) (nhds L) ∧ L ≤ maxMI N) ∧
    nsCapacity false N = eaCapacity N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end

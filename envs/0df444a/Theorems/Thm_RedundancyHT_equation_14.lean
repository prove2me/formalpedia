-- Prove2me | Theorems.Thm_RedundancyHT_equation_14
-- name    : RedundancyHT.equation_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:51.513194+00:00
-- url     : https://prove2.me/theorems/665d764b-f4ab-4b56-8fca-cf6b400a1702
-- title:
--   (14), p.18: the c.o.c. transform limit
-- statement:
--   Let $\mathcal T^*$ be the critical subset, and let $(Q_S)_{S\in\mathcal S}$ have the stationary distribution of the cancel-on-completion chain at $\lambda<\lambda^*$. For all $t_S\ge0$,
--   $$\mathbb E\Bigl[\exp\Bigl(-\bigl(1-\tfrac{\lambda}{\lambda^*}\bigr)\sum_{S\in\mathcal S}t_SQ_S\Bigr)\Bigr]\longrightarrow\Bigl(1+\sum_{S\in\mathcal T^*}\frac{p_S}{p_{\mathcal T^*}}t_S\Bigr)^{-1}$$
--   as $\lambda\uparrow\lambda^*$.
--
--   Together with the transform of the limit vector and the continuity theorem, this gives the c.o.c. half of the main theorem.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: the stationary distribution of the c.o.c. system → every family of stationary laws on (0, λ*); reason: equation_3 shows that there is exactly one law at each λ
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (14), p.18

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_cocStationary
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_scaledLaw
import Definitions.Def_RedundancyHT_laplace

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The c.o.c. transform limit (14)** (arXiv:2005.14566v5, p.18), for every stationary family. -/
theorem equation_14 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T)
    (π : ℝ → List (Fin n) → ℝ≥0∞)
    (hπ : ∀ lam, 0 < lam → lam < lamStar D T → cocStationary D (load D lam) (π lam))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Tendsto
      (fun lam => laplace (scaledLaw (π lam) (fun c i => c.count i) (1 - lam / lamStar D T)) t)
      (𝓝[<] lamStar D T) (𝓝 (1 + ∑ i ∈ T, pOf D i / pSet D T * t i)⁻¹) := by sorry

end RedundancyHT

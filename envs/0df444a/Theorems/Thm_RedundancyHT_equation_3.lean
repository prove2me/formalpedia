-- Prove2me | Theorems.Thm_RedundancyHT_equation_3
-- name    : RedundancyHT.equation_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:12.661007+00:00
-- url     : https://prove2.me/theorems/8de9fc42-0897-46c8-aa66-7e567ddd88cc
-- title:
--   (3)–(4), p.7: the c.o.c. stationary distribution
-- statement:
--   Let $\lambda>0$ satisfy the stability conditions (1). The weights
--   $$w(c)=\prod_{i=1}^{M}\frac{N\lambda p_{c_i}}{\mu(c_1,\dots,c_i)},\qquad c=(c_1,\dots,c_M),$$
--   are positive and summable over all finite sequences of job types, and
--   $$\pi_{\mathrm{c.o.c.}}(c)=C\,w(c),\qquad C=\Bigl(\sum_{c}w(c)\Bigr)^{-1},$$
--   is the unique stationary law of the cancel-on-completion chain.
--
--   The paper cites this product form from Gardner et al. It is the starting point of the generating-function analysis.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the stationary distribution → the normalized weights are stationary and every stationary law equals them; reason: the word the asserts uniqueness, and the chain is irreducible because every p_S is positive
--   - encoding: the stability conditions (1) and (2) → StabilityOne, i.e. (1); reason: (1) and (2) are equivalent, which is equations_1_2
--   - encoding: a sum and a quotient that are tacitly well defined → the conclusion also asserts summability and that every inverted quantity is non-zero; reason: Lean's tsum and inverse return junk otherwise; these are added conclusions and exclude nothing
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (3), with (4), p.7 (the paper cites Gardner et al. [28])

import Definitions.Def_RedundancyHT_cocStationary
import Definitions.Def_RedundancyHT_cocWeight
import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_load

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The stationary distribution (3) of the c.o.c. system**, from Gardner et al.
(arXiv:2005.14566v5, display (3), with (4), p.7): under the stability conditions the weights of (3)
are summable, their normalization is stationary, and every stationary law equals it.

**Formalization Note.** `C = (Σ_c weight c)⁻¹`, and `C` is the mass of the empty state since the
empty product is `1`. Uniqueness is the word "the" on the page: every `p_S` is positive, so the
chain is irreducible on all sequences. -/
theorem equation_3 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (lam : ℝ) (hlam : 0 < lam) (h : StabilityOne D lam) :
    Summable (cocWeight D lam) ∧
      (∀ c, 0 < cocWeight D lam c) ∧
      cocStationary D (load D lam)
        (fun c => ENNReal.ofReal (cocWeight D lam c / ∑' c', cocWeight D lam c')) ∧
      ∀ p, cocStationary D (load D lam) p →
        p = fun c => ENNReal.ofReal (cocWeight D lam c / ∑' c', cocWeight D lam c') := by sorry

end RedundancyHT

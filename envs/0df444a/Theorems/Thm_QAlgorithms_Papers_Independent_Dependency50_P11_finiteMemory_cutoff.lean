-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_finiteMemory_cutoff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.finiteMemory_cutoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:38:28.530977+00:00
-- url     : https://prove2.me/theorems/940813bf-734f-4d97-b1fb-ac9d7aa696cc
-- title:
--   A finite memory has a quantitative repeatability cutoff
-- statement:
--   Let $d,m\ge1$, and let $\mathcal E$ be a nonunital completely positive, trace-preserving linear map on operators on $\mathbb C^d$. Define its maximum entropy decrease by
--
--   $$\Delta_{\max}(\mathcal E)=\max_{\rho\ge0,\ \operatorname{Tr}\rho=1}\bigl[S(\rho)-S(\mathcal E(\rho))\bigr].$$
--
--   Entropies use natural logarithms. This maximum exists in finite dimension and is positive for a nonunital channel. There exists an integer $n\ge1$ with
--
--   $$n>\frac{\log m}{\Delta_{\max}(\mathcal E)}$$
--
--   for which no device with memory dimension $m$, one fixed unitary, and a fixed normalized initializer implements $\mathcal E$ on its first $n$ output marginals for all product-input histories without reset.
--
--   This gives a finite-horizon obstruction at each fixed memory size.
--
--   **Formalization Note** The maximum is represented by the supremum of its nonempty bounded set of entropy decreases, computed from $\mathcal E$.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Section III, paragraph after equation (3.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section III, PDF p.4: for fixed finite memory dimension, some positive horizon
above log(m)/Delta_max admits no n-repeatable implementation. Delta_max is computed
from E; its positivity is not assumed. See the source-ambiguity note for its interpretation. -/
theorem finiteMemory_cutoff {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hNU : ¬ IsUnital E)
    (m : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ Real.log (m : ℝ) / maxEntropyDecrease E < (n : ℝ) ∧
      ¬ ∃ D : MemoryDevice d m, RepeatableFor D E n := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end

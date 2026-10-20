-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_repeatedBlock_distance_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.repeatedBlock_distance_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:59:10.966171+00:00
-- url     : https://prove2.me/theorems/3668d6dc-bdc3-4657-a20e-c6be154c4ced
-- title:
--   Repeating an imperfect preparation block drives distance to two
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   Fix an integer $n\ge1$ and a density operator $\sigma$ on $A^{\otimes n}:B^{\otimes n}$. Suppose $\epsilon=D(\rho^{\otimes n},\sigma)>0$; the state assumptions imply $\epsilon\le2$. Then
--
--   $$\lim_{k\to\infty}D\bigl((\rho^{\otimes n})^{\otimes k},\sigma^{\otimes k}\bigr)=2.$$
--
--   Thus repeating a fixed imperfect block need not give a good approximation at growing block lengths.
--
--   **Formalization Note** The printed intermediate finite-$k$ expression uses $1-\epsilon^2$. Under the source definition of $D$, the correct factor is $1-\epsilon^2/4$. The Lean theorem states the unchanged limiting conclusion; nested copies differ from $\rho^{\otimes nk}$ only by a common local basis relabeling.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 5, Eq.(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.5, Eq.(22): repeating an imperfect block drives distance to 2.
Source correction: printed 1-epsilon^2 must read 1-epsilon^2/4 because
D=2 sqrt(1-F). Only the unchanged limiting conclusion is asserted here.
Nested copies represent rho^(n*k) up to a local basis relabeling.
The upper bound epsilon<=2 follows from the density hypotheses. -/
theorem repeatedBlock_distance_limit {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n)
    (sigma : Op (Fin (a ^ n) × Fin (b ^ n))) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (herror : paperBures (a ^ n) (b ^ n) (dimensionedPower rho n) sigma = epsilon) :
    Filter.Tendsto
      (fun k : ℕ => paperBures _ _ (dimensionedPower (dimensionedPower rho n) k) (dimensionedPower sigma k))
      Filter.atTop (nhds (2 : ℝ)) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42

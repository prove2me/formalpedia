-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_replacement_asymptotic_reduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.replacement_asymptotic_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:04:50.593075+00:00
-- url     : https://prove2.me/theorems/7113b95d-3d9d-4927-9d3c-0bd7f20278e5
-- title:
--   Replacement-channel regularization reduces to conditional von Neumann entropy
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\rho^{A_1B_1}$ be a density matrix and let $\Psi^{AB}(X)=\operatorname{Tr}(X)\rho$. Define $H_{\min}^{{\rm ext},\epsilon}(B|A)_\Psi$ as the supremum of the primal extended entropy over CPTP maps within diamond distance $\epsilon$ of $\Psi$. For $0<\epsilon<1$ the normalized tensor-power sequence has an inner limit $g(\epsilon)$, and
--   $$\lim_{\epsilon\downarrow0}g(\epsilon)=S(\rho^{A_1B_1})-S(\rho^{A_1}),\qquad g(\epsilon)=\lim_{n\to\infty}\frac1n H_{\min}^{{\rm ext},\epsilon}(B^n|A^n)_{\Psi^{\otimes n}}.$$
--   All logarithms are base two, and $n\ge1$. Both limits are stated as convergence assertions with an existential inner-limit function. This asserts the regularized value only for replacement channels. The cited input is the state AEP [52], also listed as [41].
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 21, Sec. VI, continued p.22

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.21–22, Sec.VI: replacement channels ONLY have this
regularized value. State AEP provenance: [52]=[41], arXiv:0811.1221, Theorem 1, PDF p.2.
Every inner sequence uses n+1>=1, and epsilon approaches zero from the right. -/
theorem replacement_asymptotic_reduction (A B : System) (R : Mat (Out A × Out B))
    (hR : QAlgorithms.IsDensityMatrix R) :
    ∃ f : ℝ → ℝ,
      (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        Filter.Tendsto (fun n : ℕ =>
          smoothExtended (powerSystem A (n + 1)) (powerSystem B (n + 1))
            (powerBipartite (replacementChoi A B R) (n + 1)) epsilon / (n + 1 : ℝ))
          Filter.atTop (nhds (f epsilon))) ∧
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (conditionalVonNeumann R)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end

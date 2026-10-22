-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_weight_optimality
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_weight_optimality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:46:23.853409+00:00
-- url     : https://prove2.me/theorems/ee7eba01-94d8-4e6a-91a1-368d8e2889e4
-- title:
--   §5.2: all-partial-trace optimality
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For positive odd $n$, define
--   $$F_n(h)=\sum_{k=0}^h\frac{\binom nk-\binom n{k-1}}{\binom nh}\frac{n-h-k}{n-2k}.$$
--   For every nonempty set $H\subseteq\{0,\ldots,\lfloor n/2\rfloor\}$ of allowed minority weights, the all-partial-trace template is optimal and its optimal fidelity is the attained minimum $\min_{h\in H}F_n(h)$. Taking all weights gives unrestricted majority.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 37, §5.2: all-partial-trace optimality

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.37, (5.5)-(5.6): all-partial-trace optimality for every nonempty
allowed set of minority weights; includes unrestricted majority by taking all
weights. The optimum is a minimum, with attainment. -/
theorem majority_weight_optimality (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (H : Finset ℕ) (hH : H.Nonempty) (hbound : ∀ h ∈ H, h ≤ n/2) :
    IsFunctionOptimal (fun x => min (booleanWordWeight x) (n-booleanWordWeight x) ∈ H) (majority n)
      (template alpha (fun _ => 1)) ∧
    IsLeast {r | ∃ h ∈ H, r = majorityWeightFidelity n h}
      (optimalFunctionFidelity (fun x => min (booleanWordWeight x) (n-booleanWordWeight x) ∈ H) (majority n)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end

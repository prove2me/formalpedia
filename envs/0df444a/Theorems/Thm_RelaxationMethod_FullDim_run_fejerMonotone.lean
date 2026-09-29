-- Prove2me | Theorems.Thm_RelaxationMethod_FullDim_run_fejerMonotone
-- name    : RelaxationMethod.FullDim.run_fejerMonotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:26:03.260642+00:00
-- url     : https://prove2.me/theorems/d7ea2196-dbb1-4087-ad12-f81f86abf90e
-- title:
--   §5 — an infinite relaxation sequence is Fejér-monotone with respect to $A$
-- statement:
--   Let $A$ be the nonempty solution polytope of a system of linear inequalities in $E_n$ and let $0 < \lambda \le 2$. If $p_0, p_1, p_2, \dots$ is a run of the relaxation process with parameter $\lambda$ that never terminates, i.e. $p_\nu \notin A$ for every $\nu$, then the sequence $\{p_\nu\}$ is Fejér-monotone with respect to $A$:
--
--   $$
--   p_\nu \ne p_{\nu+1}, \qquad |p_{\nu+1} - a| \le |p_\nu - a| \quad \text{for all } a \in A,\ \nu \ge 0 .
--   $$
--
--   This is the link between the relaxation process and Lemma 1, which is a statement about Fejér-monotone sequences.
--
--   **Formalization Note** The paper states this in §5 ("As already mentioned in § 1") for the case $r = n$, $0 < \lambda < 2$, and uses it again in §6 for $\lambda = 2$; we state it for $0 < \lambda \le 2$ and without the dimension hypothesis, which the claim does not use. The parameter $\lambda$ is named `lam`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 398, §5 (and §1, pp. 393–394)

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
open Filter Topology

namespace RelaxationMethod.FullDim

/-- §5, p. 398 (from §1): an infinite run of the relaxation process with `0 < lam ≤ 2`,
i.e. one that never enters the nonempty polytope `A`, is Fejér-monotone with respect to `A`. -/
theorem run_fejerMonotone {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsRelaxRun a b lam p)
    (hinf : ∀ ν : ℕ, p ν ∉ polytope a b) :
    IsFejerMonotone (polytope a b) p := by sorry

end RelaxationMethod.FullDim

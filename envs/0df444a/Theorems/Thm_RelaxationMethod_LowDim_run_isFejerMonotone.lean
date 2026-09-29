-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_run_isFejerMonotone
-- name    : RelaxationMethod.LowDim.run_isFejerMonotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:29:41.121196+00:00
-- url     : https://prove2.me/theorems/981c3125-81ba-41a7-98d2-708b4ab8acad
-- title:
--   §1 — an infinite relaxation sequence with $0 < \lambda \leqslant 2$ is Fejér-monotone
-- statement:
--   Let $A = \bigcap_i H_i$ be the solution polytope of a system of linear inequalities, assumed nonempty, and let $0 < \lambda \leqslant 2$. Let $p_0, p_1, \dots$ be an infinite sequence produced by the relaxation process: every $p_\nu$ lies outside $A$, and $p_{\nu+1}$ is obtained from $p_\nu$ by a relaxation step with parameter $\lambda$. Then $\{p_\nu\}$ is Fejér-monotone with respect to $A$:
--   $$p_\nu \neq p_{\nu+1}, \qquad |p_\nu - a| \geqslant |p_{\nu+1} - a| \quad (a \in A,\ \nu = 0, 1, \dots).$$
--
--   This observation from §1 is the link between the process and Lemma 1, and is used in the proofs of Theorems 1 and 2.
--
--   **Formalization Note** The paper argues for $0 < \lambda < 2$ (strict inequality for $a$ in $H_j$) and notes that for $\lambda = 2$ (1.1) holds with equality allowed; the statement covers the whole range $0 < \lambda \leqslant 2$ with the non-strict inequality (2.2), as §5 and §8 use it. The run is a sequence $p$ with a relaxation step after every point outside $A$, together with the hypothesis that no point lies in $A$.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, pp. 393–394, §1 (restated p. 398, §5)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_RelaxStep
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone

namespace RelaxationMethod.LowDim

/-- §1, pp. 393–394 (restated in §5, p. 398): an infinite sequence produced by the relaxation
process with `0 < λ ⩽ 2` is Fejér-monotone with respect to the (nonempty) polytope `A`. -/
theorem run_isFejerMonotone {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ polytope a b → IsRelaxStep a b lam (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ polytope a b) :
    RelaxationMethod.Shared.IsFejerMonotone (polytope a b) p := by sorry

end RelaxationMethod.LowDim

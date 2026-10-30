-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_optimal_probabilistic_mpbt
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.optimal_probabilistic_mpbt
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:59:42.561908+00:00
-- url     : https://prove2.me/theorems/33af59e6-c431-40fc-b071-961c47281a4b
-- title:
--   Theorem 23: optimal probabilistic MPBT and optimal effects
-- statement:
--   Let $d\ge1$, $k\ge1$, and $N\ge2k$. The resource is $N$ normalized Bell pairs, and outcomes are ordered injective $k$-tuples of ports. Put $L=N!/(N-k)!$. For height-bounded shapes $\alpha\vdash_d N-k$ and $\mu\vdash_d N$ with a saturated path $\alpha\to\mu$, define
--
--   $$
--   \lambda_\mu(\alpha)=\frac{L}{d^N}\frac{m_\mu d_\alpha}{m_\alpha d_\mu},\qquad
--   b_\alpha=\min_{\mu\supset\alpha}\frac1{\lambda_\mu(\alpha)}.
--   $$
--
--   Here the dimensions and multiplicities are the actual physical Schur–Weyl quantities. The minimum is over a finite nonempty set. Define on the unused registers
--
--   $$
--   \Theta_* = d^{k-N}\sum_\alpha b_\alpha P_\alpha,\qquad
--   \Pi_i=P^+_{A_iC}\otimes\Theta_*,\qquad
--   \Pi_0=I-\sum_i\Pi_i.
--   $$
--
--   These effects are feasible and attain
--
--   $$
--   p_* = \frac{L}{d^{2N}}\sum_{\alpha\vdash_d N-k}m_\alpha d_\alpha b_\alpha.
--   $$
--
--   Every family $P^+_{A_iC}\otimes\Theta_i$ with $\Theta_i\succeq0$ and positive failure effect has average success probability at most $p_*$. This is the optimum over all perfect-success measurements for the fixed resource. All selected/unused register enumerations exist, and the result holds for every such enumeration.
--
--   **Formalization Note** Printed (142) has an incorrect individual-effect prefactor. The coefficient used here is the saturating value from (143)–(145), confirmed by the matching dual value (149). Independent moderation of this correction is pending.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 19, Theorem 23

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Theorem 23: the explicit perfect-success effects attain the optimum over
all feasible measurements for the fixed Bell resource. The proof-supported
correction to printed (142) is in optimalTheta; no optimization over resources
or covariance hypothesis is imposed (PDF pp.19-20, (141),(143)-(149)). -/
theorem optimal_probabilistic_mpbt (d r k : ℕ) (hd : 0 < d)
    (hk : 0 < k) (hports : k ≤ r) :
    Nonempty (PortFrames (r+k) k r) ∧
    ∀ frames : PortFrames (r+k) k r,
      FeasibleSuccess frames (fun _ => optimalTheta d r k) ∧
      mpbtAverageSuccess frames (fun _ => optimalTheta d r k) = successExpression d r k ∧
      (∀ theta : (i : PortChoice (r+k) k) → Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ,
        FeasibleSuccess frames theta → mpbtAverageSuccess frames theta ≤ successExpression d r k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO16_quantumNonsmoothOptimization
-- name    : QAlgorithms.Papers.RoadmapO16.quantumNonsmoothOptimization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:41:52.48901+00:00
-- url     : https://prove2.me/theorems/f06b9866-4bf0-4a89-b4ef-72eafc1b34c5
-- title:
--   Quantum nonsmooth convex optimization: projected subgradients and mirror descent
-- statement:
--   Let \(X\subseteq\mathbb R^d\) be closed, bounded and convex, let \(x_1\in X\), and let \(f:\mathbb R^d\to\mathbb R\) be convex and ambient \(G\)-Lipschitz in the stated norm. Assume an attained constrained optimum \(x^\star\), and \(0<\varepsilon<1\). Both branches use coherent binary evaluations on sufficiently fine finite translated hypergrids: every grid index is preserved, the encoded value has error strictly below \(\theta\), and calls to the unitary and its adjoint are counted. The algorithm construction is fixed before the objective, optimum and oracle values; only geometry and supplied numerical scale bounds enter its construction.
--
--   1. **Euclidean branch.** Set \(R=\|x_1-x^\star\|_2\), \(K=\operatorname{diam}_2(X)\), \(T=\max\{1,\lceil(3GR/\varepsilon)^2\rceil\}\), \(r_1=\varepsilon/(6G\sqrt d)\), \(\rho=1/(3T)\), and \(\eta=R/(G\sqrt T)\). QPSM uses the actual Jordan subgradient-output law of Lemma A.1 at each current center, followed by the supplied exact Euclidean projection. For positive \(d,G,R,\theta\), impose \(\theta\le r_1dG/\rho\) and the independent-diameter precision budget
--   \[
--   23^4\frac{\theta d^4R}{\sqrt T\,\rho r_1}
--    +(23d)^2K\sqrt{\frac{\theta G}{\rho r_1}}\le\frac{\varepsilon}{3}.
--   \]
--   A sufficient scale is a small absolute constant times
--   \[
--   \min\left\{\frac{\varepsilon^3}{G^2R^2d^{9/2}},
--   \frac{\varepsilon^5}{G^4R^2K^2d^{9/2}},
--   \frac{r_1dG}{\rho}\right\}.
--   \]
--
--   2. **Mirror branch.** Fix \(p\in[1,\infty]\), \(p\ne2\), and its Hölder-conjugate exponent. Let \(P\) be open convex, \(X\subseteq\overline P\), \(X\cap P\ne\varnothing\), and \(x_1,x^\star\in X\cap P\). The supplied mirror map \(\Phi\) is strictly convex and differentiable on \(P\), its gradient takes every dual value and diverges at the boundary, and it is \(\mu\)-strongly convex on \(X\cap P\) in the chosen norm, with \(\mu>0\). Exact inverse-gradient operations and attained Bregman projections are supplied. Define \(R=\sqrt{D_\Phi(x^\star,x_1)}\), \(K=\operatorname{diam}_p(X)\), \(T=\max\{1,\lceil(6GR/(\sqrt\mu\varepsilon))^2\rceil\}\), \(r_1=\varepsilon/(6G\vartheta)\), \(\rho=1/(3T)\), and \(\eta=(R/G)\sqrt{\mu/T}\). Here \(1\le\vartheta,\vartheta_\star\le d\), \(\vartheta\vartheta_\star\le d\), \(\|v\|_p\le\vartheta\|v\|_\infty\), and \(\|g\|_\star\le\vartheta_\star\|g\|_\infty\). Require \(\theta\le r_1dG/\rho\) and
--   \[
--   \frac{2GR}{\sqrt{\mu T}}
--   +23^2\vartheta_\star K\sqrt{\frac{\theta d^3G}{\rho r_1}}
--   +2G\vartheta r_1
--   +23^4\vartheta_\star^2\frac{R}{\sqrt{\mu T}}\frac{\theta d^3}{\rho r_1}
--   \le\varepsilon.
--   \]
--   This retains both noise terms; a sufficient positive precision takes the minimum of the lemma guard and small absolute multiples of \(\mu\varepsilon^5/(G^4R^2K^2\vartheta_\star^2\vartheta d^3)\) and \(\mu\varepsilon^3/(G^2R^2\vartheta_\star^2\vartheta d^3)\).
--
--   In either branch the classical output is the average of the first \(T\) iterates, and
--   \[
--   \Pr[\bar x\in X,\ f(\bar x)-f(x^\star)\le\varepsilon]\ge2/3.
--   \]
--   The query costs are \(O(T\max\{1,\log(3dT)\})\), with absolute constants common to all data, yielding \(\widetilde O((GR/\varepsilon)^2)\) and \(\widetilde O((GR/(\sqrt\mu\varepsilon))^2)\), respectively. Quantum arithmetic uses \(\widetilde O(dT)\) gates, with binary word length and inverse precision exposed as polynomial arithmetic factors. Supplied geometric operations cost at most \(T(T_\Pi+1)\) and \(TT_{\rm next}\), respectively. All bounds apply on positive-probability branches. Conditional per-call failure control suffices; independence is not assumed.
--
--   Zero-dimensional, constant-objective, zero-radius, singleton, or already-accurate regimes return the feasible start with zero queries before divisions. In particular, a start is already accurate if \(\varepsilon\ge GK\), or \(\varepsilon\ge GR\) in the Euclidean branch, or \(\varepsilon\ge GR\sqrt{2/\mu}\) in the mirror branch.
--
--   The result shows that quantum zeroth-order methods attain the corresponding first-order nonsmooth query rates. **Formalization Note:** This uses the formal appendix scope, including ambient Lipschitz control, rather than the informal “on \(X\)” access description. The Euclidean precision corrects B.3's omitted independent \(K\); its printed \(R^4\) denominator follows in the domain-radius regime \(K\le2R\), which is not implied by an initial distance. The mirror radius is computed from the Bregman divergence, not introduced by an arbitrary equality. The finite-grid compilation and adaptive execution definitions are submitted for local definition review.
-- source:
--   Fast Convex Optimization with Quantum Gradient Methods, arXiv:2503.17356v2, Theorem 2.1; formal Theorems B.3 and C.1, PDF p. 6. https://arxiv.org/abs/2503.17356v2 . PDF SHA-256: a53928a9f3f623ede447f3f1c61aa2718e4318c1bc999833ef9bbee625859d88.

import Definitions.Def_QAlgorithms_Defs_NoisyOptimizationPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapO16_Model
set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO16

open QAlgorithms.ValueAccess QAlgorithms.NoisyOptimization




















/-- Theorem 2.1 (PDF p.6), retaining both QPSM (B.3, pp.29–30) and QMD
(C.1, pp.32–34): classical feasible epsilon-optimal averages with probability 2/3,
O-tilde((G R / epsilon)^2) and O-tilde((G R / (sqrt(mu) epsilon))^2) queries,
and the gate bounds with supplied geometry costs. Constants precede all data.
Correction: B.3's independent diameter K remains in the proof's precision budget;
the printed R^4 simplification needs a domain-radius bound. C.1 retains mu, K,
vartheta, varthetaDual and the last noise term. Ambient Lipschitz control follows
the appendix, stronger than the informal 'on X'. Trivial regimes output x1.
-/
theorem quantumNonsmoothOptimization :
    ∃ C : ℝ, 0 < C ∧ ∃ power : ℕ, ProjectedContract C power ∧ MirrorContract C power := by sorry



end QAlgorithms.Papers.RoadmapO16

-- Prove2me | Theorems.Thm_SDDiP_LagCut_tightness
-- name    : SDDiP.LagCut.tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:10.70189+00:00
-- url     : https://prove2.me/theorems/71bb4d02-b5e9-462f-8991-815b078cd0dc
-- title:
--   Proof of Theorem 3, display after (4.5) — Lagrangian cuts are tight: $\mathcal L^i_n(\hat\pi) + \hat\pi^\top\hat x = \underline Q^i_n(\hat x, \psi^{i+1}_n)$
-- statement:
--   Let $n$ be a node in iteration $i$ with the data of the node definition, and assume $X''_n$ is nonempty. Let $\hat x \in \{0,1\}^d$ be the binary forward-step state of the parent, let $\hat\pi$ be an optimal solution of the Lagrangian dual (4.3) at $\hat x$, and put $\hat v = \mathcal L^i_n(\hat\pi)$. Then the Lagrangian cut $(\hat v, \hat\pi)$ is tight at $\hat x$ in the sense of (3.5):
--
--   $$\hat v + \hat\pi^\top \hat x = \underline Q^i_n(\hat x, \psi^{i+1}_n) = \min\big\{ f_n(x,y) + \psi^{i+1}_n(x) : (z,x,y) \in X_n,\ z = \hat x,\ x \in \{0,1\}^d\big\},$$
--
--   and the minimum of the updated forward problem (3.1) is attained.
--
--   Tightness is the property that makes SND/SDDiP with Lagrangian cuts exact: at the state where the cut is generated, the cut reproduces the value of the current approximation.
--
--   **Formalization Note** The approximation is $\psi^{i+1}_n$, built from the cuts $\ell = 1,\dots,i$ that also define $X''_n$; the last line of the paper's display writes $\psi^i_n$, a misprint for $\psi^{i+1}_n$ (definition (3.5) and $X''_n$ both use the cuts up to $i$). The conclusion is stated twice: as `IsLeast` of the set of forward objective values (attained minimum), and as equality with the `sInf`-defined value $\underline Q^i_n$. Binarity of $\hat x$ is essential (Example 1, p. 480).
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 479, proof of Theorem 3, display after (4.5); (3.5), p. 473

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- Tightness of the Lagrangian cut (3.5): proof of Theorem 3, display after (4.5), p. 479 (Zou, Ahmed,
Sun, Math. Program. 175 (2019)). For a binary parent state `x̂` and an optimal solution `π̂` of the
Lagrangian dual (4.3), `𝓛^i_n(π̂) + π̂ᵀx̂` is the (attained) optimal value `Q̲^i_n(x̂, ψ^{i+1}_n)` of the
updated forward problem (3.1). `X″_n` is assumed nonempty, so that `𝓛^i_n` is a genuine minimum. -/
theorem tightness {d l : ℕ} (N : Node d l) (xhat : Fin d → ℝ) (hxhat : IsBinary xhat)
    (hX' : N.X'.Nonempty) (πhat : Fin d → ℝ) (hopt : N.IsDualOptimal xhat πhat) :
    IsLeast (N.fwdValues xhat) (N.lag πhat + πhat ⬝ᵥ xhat) ∧
      N.fwdValue xhat = N.lag πhat + πhat ⬝ᵥ xhat := by sorry

end SDDiP.LagCut

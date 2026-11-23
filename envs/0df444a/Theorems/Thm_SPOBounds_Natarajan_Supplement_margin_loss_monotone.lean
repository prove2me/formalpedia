-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_Supplement_margin_loss_monotone
-- name    : SPOBounds.Natarajan.Supplement.margin_loss_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:37:50.120391+00:00
-- url     : https://prove2.me/theorems/0de74c09-0e93-48a2-b7ec-96f5524640d1
-- title:
--   §4.1, p. 15 — the $\gamma$-margin SPO loss is nondecreasing in $\gamma$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty, compact, convex feasible region that is not a singleton, and let $w^*$ be any optimization oracle for $S$, so that $w^*(c)\in\arg\min_{w\in S}c^\top w$ for every $c$. For $\gamma>0$ write $\ell^\gamma_{\rm SPO}(\hat c,c)$ for the $\gamma$-margin SPO loss of Definition 4: it equals the SPO loss $\ell_{\rm SPO}(\hat c,c)=c^\top w^*(\hat c)-c^\top w^*(c)$ when the distance to degeneracy satisfies $\nu_S(\hat c)>\gamma$, and
--   $\frac{\nu_S(\hat c)}{\gamma}\ell_{\rm SPO}(\hat c,c)+\bigl(1-\frac{\nu_S(\hat c)}{\gamma}\bigr)\omega_S(c)$ otherwise, where $\omega_S(c)$ is the linear optimization gap.
--
--   Then for every prediction $\hat c$, every cost vector $c$ and all $\bar\gamma\ge\gamma>0$,
--   $$\ell^\gamma_{\rm SPO}(\hat c,c)\le\ell^{\bar\gamma}_{\rm SPO}(\hat c,c).$$
--
--   This monotonicity lets the proof of Theorem 5 compare the empirical margin risk at a grid point $\gamma_k\le\gamma$ with the one at $\gamma$.
--
--   **Formalization Note** The space $\mathbb R^d$ with a generic norm is a finite-dimensional real normed space $E$, and cost vectors are continuous linear functionals on $E$, so $c^\top w$ is $c(w)$ and the operator norm is the dual norm. The margin loss is the published `SPOBounds.Margin.marginLoss`.
--
--   Differences from the source:
--   - encoding: $\hat c, c\in\mathbb R^d$ with a generic norm → continuous linear functionals on a finite-dimensional normed space $E$; reason: $c^\top w$ is $c(w)$ and the operator norm is the dual norm, so every instance of the source is an instance of the Lean statement and conversely.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 15, §4.1 (monotonicity sentence after Definition 4)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

open SPOBounds.Margin

namespace SPOBounds.Natarajan.Supplement

/-- **§4.1, p. 15, monotonicity of the `γ`-margin SPO loss** (arXiv:1905.11488v3). Let `S` be a
nonempty, compact, convex feasible region in a finite-dimensional normed space (the paper's `ℝ^d`
with a generic norm) that is not a singleton (Section 4, p. 13), and `w` any optimization oracle.
Then for every prediction `ĉ`, every cost `c` and all `γ̄ ≥ γ > 0`,
`ℓ^γ_SPO(ĉ, c) ≤ ℓ^γ̄_SPO(ĉ, c)`. -/
theorem margin_loss_monotone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (γ γbar : ℝ) (hγ : 0 < γ) (hγγ : γ ≤ γbar)
    (chat c : StrongDual ℝ E) :
    marginLoss S w γ chat c ≤ marginLoss S w γbar chat c := by sorry

end SPOBounds.Natarajan.Supplement

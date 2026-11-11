-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_3_3
-- name    : SensLabelCover.DH.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:23.011751+00:00
-- url     : https://prove2.me/theorems/214aa7e2-d11a-4347-adea-43e24d33578a
-- title:
--   Lemma 3.3 — a pointwise recovery that is $C_{\mathcal R}$-Lipschitz and $D_{\mathcal R}$-stable lifts to distributions with the same constants
-- statement:
--   Let $\mathcal X$ be a family of source instances with a one-swap relation, let outputs be compared by costs $d_X,d_Y$, and let $R_I$, for each instance $I$, map each target output $y$ to a distribution $R_I(y)$ on source outputs. Suppose that
--   $$\mathrm{EMD}(R_I(y),R_I(\tilde y))\le C_{\mathcal R}\,d_Y(y,\tilde y)\quad(I\in\mathcal X,\ \text{all }y,\tilde y),\qquad \mathrm{EMD}(R_I(y),R_{\tilde I}(y))\le D_{\mathcal R}$$
--   for all neighbouring $I,\tilde I\in\mathcal X$ and every $y$. Then the induced recovery on distributions $\mu\mapsto(R_I)_\#\mu=\sum_y\mu(y)R_I(y)$ satisfies $\mathrm{EMD}((R_I)_\#\mu,(R_I)_\#\nu)\le C_{\mathcal R}\,\mathrm{EMD}(\mu,\nu)$ for $I\in\mathcal X$ and all $\mu,\nu$, and $\mathrm{EMD}((R_I)_\#\mu,(R_{\tilde I})_\#\mu)\le D_{\mathcal R}$ for neighbouring $I,\tilde I\in\mathcal X$ and every $\mu$.
--
--   The lemma reduces the two recovery conditions of Definition 3.1 to statements about single outputs.
--
--   Differences from the source:
--   - generalization: Hamming distance on outputs → arbitrary real costs $d_X,d_Y$; reason: the Hamming distance is one such cost, so the statement specializes to the paper's.
--   - generalization: "for every $I$" → for every $I$ in a given family $\mathcal X$ (hypotheses and conclusion relative to $\mathcal X$); reason: taking $\mathcal X$ to be all instances gives the paper's statement.
--   - encoding: $(R_I)_\#\mu$ → `μ.bind (R I)`; abstract instance and output types; reason: same objects.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 19 (PDF 22), Lemma 3.3

import Mathlib
import Definitions.Def_SensLabelCover_DH_Sensitivity

namespace SensLabelCover.DH

/-- Lemma 3.3 (Lifting a pointwise recovery to distributions), p. 19 (PDF p. 22). A pointwise
recovery `R I : Y → D(X)` induces `μ ↦ (R_I)_#μ = μ.bind (R I)`. Source instances form a type
`S` with one-swap relation `adjS` and a family `𝓧`; outputs are finite types compared by costs
`dX`, `dY` (the Hamming distance in the paper). -/
theorem lemma_3_3 {S OX OY : Type} [Fintype OX] [Fintype OY] (adjS : S → S → Prop)
    (dX : OX → OX → ℝ) (dY : OY → OY → ℝ) (𝓧 : Set S) (R : S → OY → PMF OX) (CR DR : ℝ)
    (hLip : ∀ I ∈ 𝓧, ∀ y y' : OY, emd dX (R I y) (R I y') ≤ CR * dY y y')
    (hStab : ∀ I ∈ 𝓧, ∀ J ∈ 𝓧, adjS I J → ∀ y : OY, emd dX (R I y) (R J y) ≤ DR) :
    (∀ I ∈ 𝓧, ∀ μ ν : PMF OY, emd dX (μ.bind (R I)) (ν.bind (R I)) ≤ CR * emd dY μ ν) ∧
      (∀ I ∈ 𝓧, ∀ J ∈ 𝓧, adjS I J → ∀ μ : PMF OY,
        emd dX (μ.bind (R I)) (μ.bind (R J)) ≤ DR) := by sorry

end SensLabelCover.DH

-- Prove2me | Theorems.Thm_SpectralContrastive_labels_cut_bound
-- name    : SpectralContrastive.labels_cut_bound
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T18:37:29.022094+00:00
-- url     : https://prove2.me/theorems/eebfe257-2826-4432-91ba-40541c686895
-- title:
--   Lemma B.5: a classifier on augmentations gives a labeling with few cut edges
-- statement:
--   Consider the finite data model and labels $y:\overline{\mathcal X}\to[r]$. Suppose a classifier $g:\mathcal X\to[r]$ on augmented data predicts the label with error at most $\alpha$:
--
--   $$\Pr_{\bar x\sim P,\,x\sim\mathcal A(\cdot\mid\bar x)}\big(g(x)\ne y(\bar x)\big)\le\alpha$$
--
--   (Assumption 3.6). Then there is an extended labeling function $\hat y:\mathcal X\to[r]$ with
--
--   $$\Delta(y,\hat y)\le\alpha\qquad\text{and}\qquad\phi^{\hat y}=\sum_{x,x'}w_{xx'}\mathbf 1[\hat y(x)\ne\hat y(x')]\le2\alpha.$$
--
--   The paper's $\hat y$ is the partition $S_1,\dots,S_r$ induced by $g$. The lemma turns the recoverability assumption into a bound on the edge weight crossing the classes.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Appendix B.2, Lemma B.5, eqs. (18)-(19), pp. 26-28

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem labels_cut_bound {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X] {r : ℕ}
    (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) (y : Xbar → Fin r) (α : ℝ)
    (g : X → Fin r) (hg : labelDisagree P A y g ≤ α) :
    ∃ yhat : X → Fin r, labelDisagree P A y yhat ≤ α ∧
      cutWeight (augWeight P A) yhat ≤ 2 * α := by sorry

end SpectralContrastive

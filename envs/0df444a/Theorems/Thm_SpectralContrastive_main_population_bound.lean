-- Prove2me | Theorems.Thm_SpectralContrastive_main_population_bound
-- name    : SpectralContrastive.main_population_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:38:57.597524+00:00
-- url     : https://prove2.me/theorems/5ea9853c-75eb-4556-a74f-bc762a64930d
-- title:
--   Theorem 3.8: main theorem for population pretraining data
-- statement:
--   There is a universal constant $C$ with the following property. Consider the finite data model with labels $y:\overline{\mathcal X}\to[r]$, let the representation dimension satisfy $k\ge2r$, and suppose Assumption 3.6 holds for some $\alpha>0$: some classifier $g:\mathcal X\to[r]$ has $\Pr_{\bar x\sim P,\,x\sim\mathcal A(\cdot\mid\bar x)}(g(x)\ne y(\bar x))\le\alpha$. Let $f^*_{\mathrm{pop}}$ minimize the population spectral contrastive loss $\mathcal L(f)$ over all $f:\mathcal X\to\mathbb R^k$. Then:
--
--   1. If $\rho_{\lfloor k/2\rfloor}>0$,
--   $$\mathcal E(f^*_{\mathrm{pop}})\le C\,\frac{\alpha}{\rho_{\lfloor k/2\rfloor}^2}\log k.$$
--   2. If Assumption 3.5 holds, i.e. $\rho_{m+1}\ge\rho$ for some $\rho>0$, and $k>2m$, then
--   $$\mathcal E(f^*_{\mathrm{pop}})\le C\,\frac{\alpha}{\rho^2}\log k.$$
--
--   The linear probe error of the representation learned from the population spectral contrastive loss is therefore controlled by the ratio of class separation $\alpha$ to the squared internal connectivity $\rho^2$ of the augmentation graph.
--
--   **Formalization Note** The paper writes $\mathcal E(f^*_{\mathrm{pop}})\le\widetilde O(\alpha/\rho_{\lfloor k/2\rfloor}^2)$, where $\widetilde O$ hides universal constant factors and logarithmic factors in $k$. The statement uses the form the proof establishes, $\lesssim(\alpha/\rho^2)\log k$, with one universal constant quantified before all data. The hypothesis class $\mathcal F$ of Assumption 3.7 plays no role once $f^*_{\mathrm{pop}}$ is a global minimizer, so it is omitted. The hypothesis $\rho_{\lfloor k/2\rfloor}>0$ excludes division by zero, where the paper's bound is infinite.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Section 3.3, Theorem 3.8, p. 11; proof in Appendix B.2, p. 28

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem main_population_bound :
    ∃ C : ℝ, ∀ (Xbar X : Type) [Fintype Xbar] [Fintype X] [DecidableEq X] (r k : ℕ)
      (P : Xbar → ℝ) (A : Xbar → X → ℝ), IsAugModel P A → 2 * r ≤ k →
      ∀ (y : Xbar → Fin r) (α : ℝ), 0 < α → (∃ g : X → Fin r, labelDisagree P A y g ≤ α) →
      ∀ f : X → Fin k → ℝ, (∀ f' : X → Fin k → ℝ, scLoss P A f ≤ scLoss P A f') →
      (0 < sparsestPartition (augWeight P A) (k / 2) →
        linearProbeError P A y f ≤
          C * (α / sparsestPartition (augWeight P A) (k / 2) ^ 2) * Real.log k) ∧
      (∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ sparsestPartition (augWeight P A) (m + 1) → 2 * m < k →
        linearProbeError P A y f ≤ C * (α / ρ ^ 2) * Real.log k) := by sorry

end SpectralContrastive

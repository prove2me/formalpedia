-- Prove2me | Theorems.Thm_SpectralContrastive_error_propagation
-- name    : SpectralContrastive.error_propagation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:40:14.63685+00:00
-- url     : https://prove2.me/theorems/f4c69c42-9cb8-4106-9a2b-259bf86eba0b
-- title:
--   Theorem D.7: error propagation from pre-training to the downstream task
-- statement:
--   There is a universal constant $C$ with the following property. Consider the finite data model with $N=|\mathcal X|$ and labels in $[r]$, let $4r+2\le k\le N$, and suppose Assumption 3.6 holds for some $\alpha>0$. Let $\gamma_i$ be the $i$-th largest eigenvalue of $\overline A$ and assume that the eigengap $\Delta_\gamma:=\gamma_{\lfloor3k/4\rfloor}-\gamma_k$ and $\rho_{\lfloor k/2\rfloor}$ are positive. Let $f^*_{\mathrm{pop}}$ minimize $\mathcal L$ over all functions. Then for every $\epsilon>0$ and every $\hat f$ with $\mathcal L(\hat f)<\mathcal L(f^*_{\mathrm{pop}})+\epsilon$ there is a linear head $\widehat B\in\mathbb R^{k\times r}$ with
--
--   $$\mathcal E(\hat f,\widehat B)\le C\Big(\frac{\alpha}{\rho_{\lfloor k/2\rfloor}^2}\log k+\frac{k\epsilon}{\Delta_\gamma^2}\Big),$$
--
--   and, if $\lambda_k<1$, with $\|\widehat B\|_F\le2(k+1)/(1-\lambda_k)$. In particular $\mathcal E(\hat f)$ obeys the same bound.
--
--   The downstream error therefore grows at most linearly in the excess pretraining loss $\epsilon$.
--
--   **Formalization Note** The paper's $\lesssim$ is a universal constant $C$ quantified before all data. The paper states the theorem for $\hat f_{\mathrm{emp}}\in\mathcal F$; the class plays no role in the bound, so the statement is for every $\hat f$. The hypotheses $\rho_{\lfloor k/2\rfloor}>0$ and $\Delta_\gamma>0$ exclude division by zero, and $k\le N$ makes $\gamma_k$ an eigenvalue. The norm clause is conditional on $\lambda_k<1$, where its right side is defined.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Appendix D.3, Theorem D.7, eq. (45), pp. 41-42

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem error_propagation :
    ∃ C : ℝ, ∀ (Xbar X : Type) [Fintype Xbar] [Fintype X] [DecidableEq X] (r k : ℕ)
      (P : Xbar → ℝ) (A : Xbar → X → ℝ), IsAugModel P A → 4 * r + 2 ≤ k →
      k ≤ Fintype.card X →
      ∀ (y : Xbar → Fin r) (α : ℝ), 0 < α → (∃ g : X → Fin r, labelDisagree P A y g ≤ α) →
      0 < sparsestPartition (augWeight P A) (k / 2) →
      0 < adjEig (augWeight P A) (3 * k / 4) - adjEig (augWeight P A) k →
      ∀ fstar : X → Fin k → ℝ, (∀ f' : X → Fin k → ℝ, scLoss P A fstar ≤ scLoss P A f') →
      ∀ (ε : ℝ), 0 < ε → ∀ fhat : X → Fin k → ℝ, scLoss P A fhat < scLoss P A fstar + ε →
      ∃ B : Matrix (Fin k) (Fin r) ℝ,
        (lapEig (augWeight P A) k < 1 →
          frobNorm B ≤ 2 * (k + 1) / (1 - lapEig (augWeight P A) k)) ∧
        probeError P A y fhat B ≤
          C * (α / sparsestPartition (augWeight P A) (k / 2) ^ 2 * Real.log k +
            k * ε / (adjEig (augWeight P A) (3 * k / 4) - adjEig (augWeight P A) k) ^ 2) := by sorry

end SpectralContrastive

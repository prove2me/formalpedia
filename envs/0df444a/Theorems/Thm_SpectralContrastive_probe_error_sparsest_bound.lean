-- Prove2me | Theorems.Thm_SpectralContrastive_probe_error_sparsest_bound
-- name    : SpectralContrastive.probe_error_sparsest_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:38:27.679382+00:00
-- url     : https://prove2.me/theorems/a1c8d29f-70ef-4198-801b-0f683a8699d4
-- title:
--   Theorem B.2: generalized version of Theorem 3.8
-- statement:
--   There are universal constants $c$ and $K$ with the following property. Consider the finite data model and integers $k\ge1$ and $k'\ge\max(r,1)$ with $k+1=(1+\zeta)k'$ for some $\zeta\in(0,1)$. Let $f^*_{\mathrm{pop}}$ minimize $\mathcal L(f)$ over all $f:\mathcal X\to\mathbb R^k$, let $\hat y:\mathcal X\to[r]$ be any labeling function, and assume $\rho_{k'}>0$. Then there is a linear head $B\in\mathbb R^{k\times r}$ with
--
--   $$\mathbb E_{\bar x,x}\big[\|\vec y(\bar x)-B^\top f^*_{\mathrm{pop}}(x)\|_2^2\big]\le c\Big((1+1/\zeta)^K\log(k+1)\,\frac{\phi^{\hat y}}{\rho_{k'}^2}+\Delta(y,\hat y)\Big).$$
--
--   Every argmax prediction of this head has error $\Pr_{\bar x,x}(g_{f^*_{\mathrm{pop}},B}(x)\ne y(\bar x))$ at most twice the same right-hand side. If moreover $\lambda_k<1$, the head can be taken with $\|B\|_F\le1/(1-\lambda_k)$.
--
--   **Formalization Note** The paper's $\mathrm{poly}(1/\zeta)$ is written $(1+1/\zeta)^K$ with a universal $K$, and its universal constant $c$ is quantified before all data. The hypothesis $\rho_{k'}>0$ excludes the case where the right-hand side divides by zero. The norm clause is conditional on $\lambda_k<1$, which is where $1/(1-\lambda_k)$ is defined.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Appendix B.1, Theorem B.2, p. 26

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem probe_error_sparsest_bound :
    ∃ (c : ℝ) (K : ℕ), ∀ (Xbar X : Type) [Fintype Xbar] [Fintype X] [DecidableEq X]
      (r k k' : ℕ) (ζ : ℝ) (P : Xbar → ℝ) (A : Xbar → X → ℝ), IsAugModel P A →
      1 ≤ k → 1 ≤ k' → r ≤ k' → 0 < ζ → ζ < 1 → (k : ℝ) + 1 = (1 + ζ) * k' →
      ∀ (y : Xbar → Fin r) (yhat : X → Fin r) (f : X → Fin k → ℝ),
      (∀ f' : X → Fin k → ℝ, scLoss P A f ≤ scLoss P A f') →
      0 < sparsestPartition (augWeight P A) k' →
      ∃ B : Matrix (Fin k) (Fin r) ℝ,
        probeSqLoss P A y f B ≤
          c * ((1 + 1 / ζ) ^ K * Real.log (k + 1) * cutWeight (augWeight P A) yhat /
            sparsestPartition (augWeight P A) k' ^ 2 + labelDisagree P A y yhat) ∧
        (∀ g : X → Fin r, IsProbePred f B g →
          labelDisagree P A y g ≤
            2 * c * ((1 + 1 / ζ) ^ K * Real.log (k + 1) * cutWeight (augWeight P A) yhat /
              sparsestPartition (augWeight P A) k' ^ 2 + labelDisagree P A y yhat)) ∧
        (lapEig (augWeight P A) k < 1 → frobNorm B ≤ 1 / (1 - lapEig (augWeight P A) k)) := by sorry

end SpectralContrastive

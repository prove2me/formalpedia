-- Prove2me | Theorems.Thm_SpectralContrastive_probe_error_eigen_bound
-- name    : SpectralContrastive.probe_error_eigen_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:37:58.055267+00:00
-- url     : https://prove2.me/theorems/b268bf09-aca9-49d7-9ee2-e5d8cc36b86b
-- title:
--   Theorem B.3 (as proved): linear probe error in terms of $\lambda_{k+1}$
-- statement:
--   Consider the finite data model with $N=|\mathcal X|$, let $1\le k<N$, and let $\lambda_1\le\lambda_2\le\cdots$ be the eigenvalues of the normalized Laplacian of the augmentation graph. Assume $\lambda_{k+1}>0$ and $\lambda_k<1$. Let $f^*_{\mathrm{pop}}:\mathcal X\to\mathbb R^k$ minimize the population spectral contrastive loss $\mathcal L(f)$ over all functions. Then for every labeling function $\hat y:\mathcal X\to[r]$ there is a linear head $B\in\mathbb R^{k\times r}$ with $\|B\|_F\le1/(1-\lambda_k)$ such that
--
--   $$\mathbb E_{\bar x\sim P,\,x\sim\mathcal A(\cdot\mid\bar x)}\big[\|\vec y(\bar x)-B^\top f^*_{\mathrm{pop}}(x)\|_2^2\big]\le\frac{2\phi^{\hat y}}{\lambda_{k+1}}+4\Delta(y,\hat y),$$
--
--   and every argmax prediction $g_{f^*_{\mathrm{pop}},B}$ (any tie-breaking) satisfies
--
--   $$\Pr_{\bar x\sim P,\,x\sim\mathcal A(\cdot\mid\bar x)}\big(g_{f^*_{\mathrm{pop}},B}(x)\ne y(\bar x)\big)\le\frac{4\phi^{\hat y}}{\lambda_{k+1}}+8\Delta(y,\hat y).$$
--
--   **Formalization Note** The paper prints the constants $1$ and $2$ in front of $\phi^{\hat y}/\lambda_{k+1}$. The proof establishes $2$ and $4$: summing eq. (26) over $i\in[r]$ counts every edge $(x,x')$ with $\hat y(x)\ne\hat y(x')$ twice, so eq. (27) holds with $\phi^{\hat y}/\lambda_{k+1}$ in place of $\phi^{\hat y}/(2\lambda_{k+1})$. The statement here carries the proved constants. The hypotheses $k<N$ and $\lambda_{k+1}>0$ are those of Lemma B.6, which the proof uses. The hypothesis $\lambda_k<1$ is the domain of the printed norm bound $1/(1-\lambda_k)$. The head is the transpose of the paper's $B^*\in\mathbb R^{r\times k}$.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Appendix B.1, Theorem B.3, p. 27; proof in Appendix B.3, eqs. (25)-(28), pp. 31-32

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem probe_error_eigen_bound {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X]
    {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) (y : Xbar → Fin r)
    (hk : 1 ≤ k) (hkN : k + 1 ≤ Fintype.card X)
    (hl : 0 < lapEig (augWeight P A) (k + 1)) (hlk : lapEig (augWeight P A) k < 1)
    (f : X → Fin k → ℝ) (hf : ∀ f' : X → Fin k → ℝ, scLoss P A f ≤ scLoss P A f')
    (yhat : X → Fin r) :
    ∃ B : Matrix (Fin k) (Fin r) ℝ,
      frobNorm B ≤ 1 / (1 - lapEig (augWeight P A) k) ∧
      probeSqLoss P A y f B ≤
        2 * cutWeight (augWeight P A) yhat / lapEig (augWeight P A) (k + 1) +
          4 * labelDisagree P A y yhat ∧
      ∀ g : X → Fin r, IsProbePred f B g →
        labelDisagree P A y g ≤
          4 * cutWeight (augWeight P A) yhat / lapEig (augWeight P A) (k + 1) +
            8 * labelDisagree P A y yhat := by sorry

end SpectralContrastive

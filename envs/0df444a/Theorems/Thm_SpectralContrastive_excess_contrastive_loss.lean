-- Prove2me | Theorems.Thm_SpectralContrastive_excess_contrastive_loss
-- name    : SpectralContrastive.excess_contrastive_loss
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:39:31.514695+00:00
-- url     : https://prove2.me/theorems/eec53276-27a1-4b3d-b61d-ac13d30d1841
-- title:
--   Theorem 4.1 (corrected constant): excess contrastive loss
-- statement:
--   There is a universal constant $C$ with the following property. Consider the finite data model, a hypothesis class $\mathcal F$ of maps $\mathcal X\to\mathbb R^k$ with $\|f(x)\|_\infty\le\kappa$ for all $f\in\mathcal F$ and $x\in\mathcal X$, where $\kappa>0$. Let $f^*_{\mathrm{pop}}\in\mathcal F$ be a minimizer of the population loss $\mathcal L$ over all functions (Assumption 3.7). Let $n\ge2$ and $\delta\in(0,1)$. Draw a dataset $\bar x_1,\dots,\bar x_n$ i.i.d. from $P$. Then, with probability at least $1-\delta$, every minimizer $\hat f_{\mathrm{emp}}\in\mathcal F$ of the empirical loss $\widehat{\mathcal L}_n$ over $\mathcal F$ satisfies
--
--   $$\mathcal L(\hat f_{\mathrm{emp}})\le\mathcal L(f^*_{\mathrm{pop}})+c_1\,\widehat{\mathcal R}_{\lfloor n/2\rfloor}(\mathcal F)+c_2\Big(\sqrt{\frac{\log(2/\delta)}{n}}+\delta\Big),$$
--
--   with $c_1=C(k^2\kappa^3+k\kappa)$ and $c_2=C(k\kappa^2+k^2\kappa^4)$.
--
--   **Formalization Note** The paper prints $c_1\lesssim k^2\kappa^2+k\kappa$. That is false: in Lemma D.3 (p. 38) the map $t\mapsto t^2$ is applied to $t=f(z)^\top f(z')$ with $|t|\le k\kappa^2$, so its Lipschitz constant is $2k\kappa^2$, not $2k\kappa$, and the corrected proof gives $c_1\lesssim k^2\kappa^3+k\kappa$. For $k=1$, a single point per natural datum and $\mathcal F$ all functions bounded by $\kappa$, an empirical minimizer may take the value $\kappa$ on unsampled points, and its excess loss grows like $\kappa^4$, which exceeds the printed bound for every constant once $\kappa$ and $n$ are large. The constants $c_1$ and $c_2$ are written with one universal constant $C$. The paper's $\widehat{\mathcal R}_{n/2}$ is read as $\widehat{\mathcal R}_{\lfloor n/2\rfloor}$ for odd $n$, matching the $\lfloor n/2\rfloor$ disjoint pairs of the subsampling in Definition D.3. The conditions $n\ge2$ and $0<\delta<1$ are the domains of $1/(n(n-1))$ and $\log(2/\delta)$ in a nontrivial probability statement.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Section 4.1, Theorem 4.1, p. 14; proof in Appendix D.1, pp. 37-40

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem excess_contrastive_loss :
    ∃ C : ℝ, ∀ (Xbar X : Type) [Fintype Xbar] [Fintype X] [DecidableEq X] (k n : ℕ)
      (P : Xbar → ℝ) (A : Xbar → X → ℝ), IsAugModel P A → 2 ≤ n →
      ∀ (F : Set (X → Fin k → ℝ)) (κ : ℝ), 0 < κ → (∀ f ∈ F, ∀ x i, |f x i| ≤ κ) →
      ∀ fstar ∈ F, (∀ f' : X → Fin k → ℝ, scLoss P A fstar ≤ scLoss P A f') →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      1 - δ ≤ datasetProb P (fun d : Fin n → Xbar =>
        ∀ fhat ∈ F, (∀ f ∈ F, empLoss A d fhat ≤ empLoss A d f) →
          scLoss P A fhat ≤ scLoss P A fstar +
            C * (k ^ 2 * κ ^ 3 + k * κ) * rademacher F (n / 2) +
            C * (k * κ ^ 2 + k ^ 2 * κ ^ 4) * (Real.sqrt (Real.log (2 / δ) / n) + δ)) := by sorry

end SpectralContrastive

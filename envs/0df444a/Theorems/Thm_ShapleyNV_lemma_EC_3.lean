-- Prove2me | Theorems.Thm_ShapleyNV_lemma_EC_3
-- name    : ShapleyNV.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:57.782422+00:00
-- url     : https://prove2.me/theorems/3340b9ec-f449-4323-a583-fe672beb923f
-- title:
--   Lemma EC.3, p.ec4 — a $\lambda/(b\vee h)$-Lipschitz in-sample policy in $[\underline z_k,\overline z_k]$ that does no worse
-- statement:
--   Let $b > 0$ and $0 \le h \le b$. For each fixed $\lambda \ge b \vee h$ and each in-sample policy $\hat f \ge 0$ there is an in-sample policy $\hat g \ge 0$ such that
--
--   1. $\hat g$ is $\frac{\lambda}{b \vee h}$-Lipschitz on $\widehat{\mathcal X}$: $|\hat g(\hat x_j) - \hat g(\hat x_k)| \le \frac{\lambda}{b \vee h}\|\hat x_j - \hat x_k\|$ for all $j, k$;
--   2. $\underline z_k \le \hat g(\hat x_k) \le \overline z_k$ for all $k$, where
--   $$
--   \underline z_k := \min_{(x,z)\in\operatorname{supp}\widehat{\mathbb P}}\{z + \|x - \hat x_k\|\}, \qquad \overline z_k := \max_{(x,z)\in\operatorname{supp}\widehat{\mathbb P}}\{z - \|x - \hat x_k\|\};
--   $$
--   3. for all $(\hat x, \hat z) \in \operatorname{supp}\widehat{\mathbb P}$,
--   $$
--   \max_{x \in \widehat{\mathcal X}}\big\{\Psi(\hat g(x), \hat z) - \lambda\|x - \hat x\|\big\} \le \max_{x \in \widehat{\mathcal X}}\big\{\Psi(\hat f(x), \hat z) - \lambda\|x - \hat x\|\big\}.
--   $$
--
--   This lets the in-sample dual be minimized over a compact box of Lipschitz policies.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: (x̂, ẑ) ∈ supp P̂ → every observation pair (k', i), with x̂ = x̂_k', ẑ = ẑ_k'i; reason: supp P̂ is exactly the set of observations
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_zlow
import Definitions.Def_ShapleyNV_zup

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma EC.3**, p.ec4: for each fixed `λ ≥ b ∨ h` and `f̂ ∈ ℱ̂` there is a
`λ/(b∨h)`-Lipschitz policy `ĝ ∈ ℱ̂` with `z̲_k ≤ ĝ(x̂_k) ≤ z̄_k` such that for all `(x̂, ẑ) ∈ supp P̂`,
`max_{x∈𝒳̂} { Ψ(ĝ(x), ẑ) − λ‖x − x̂‖ } ≤ max_{x∈𝒳̂} { Ψ(f̂(x), ẑ) − λ‖x − x̂‖ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25).

**Formalization Note.** `ĝ` and `f̂` are vectors `g`, `y` indexed by `Fin K`; "`ĝ ∈ ℱ̂`" is `g ≥ 0`;
"`λ/(b∨h)`-Lipschitz" is Lipschitz on `𝒳̂`; the support of `P̂` is indexed by the observation
pairs `(k', i)`, with `x̂ = x̂_k'`, `ẑ = ẑ_k'i`. -/
theorem lemma_EC_3 {X : Type*} [MetricSpace X] (D : Data X) (h b : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (lam : ℝ) (hlam : max b h ≤ lam) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∃ g : Fin D.K → ℝ, (∀ k, 0 ≤ g k) ∧
      (∀ j k, |g j - g k| ≤ lam / max b h * dist (D.xhat j) (D.xhat k)) ∧
      (∀ k, zlow D k ≤ g k ∧ g k ≤ zup D k) ∧
      ∀ (k' : Fin D.K) (i : Fin (D.m k')),
        Finset.univ.sup' D.univ_nonempty
            (fun j => nvCost h b (g j) (D.zhat k' i) - lam * dist (D.xhat j) (D.xhat k')) ≤
          Finset.univ.sup' D.univ_nonempty
            (fun j => nvCost h b (y j) (D.zhat k' i) - lam * dist (D.xhat j) (D.xhat k')) := by sorry

end ShapleyNV

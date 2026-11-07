-- Prove2me | Theorems.Thm_PDSEquiv_lemma_6_2
-- name    : PDSEquiv.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:47.338935+00:00
-- url     : https://prove2.me/theorems/d37e98ef-bf87-4783-9784-8f279c6778a9
-- title:
--   Lemma 6.2 — amplification of a nonnegative statistic: $\Pr_{\mathrm{PDS}(n,\kappa)}[(T_{k/\kappa}w)\ge\eta/(40\sqrt k)]\ge\gamma$
-- statement:
--   Fix $0<q<p\le1$ and $A,B,\tau>0$. There are constants $\gamma>0$ and $N_0$, depending only on these parameters, such that for $N\ge N_0$: let $n,k,\kappa$ be integers with
--   $$n\le N^B,\quad 1\le k\le\kappa/2,\quad \kappa\le n/2,\quad k/\kappa\le N^{-\tau}.$$
--   Let $w:\mathcal G_n\to[0,1]$ be permutation-invariant and $\eta\ge N^{-A}$. If $\mathbb E_{G\sim\mathrm{PDS}(n,k,p,q)}[w(G)]\ge\eta$, then
--   $$\Pr_{G\sim\mathrm{PDS}(n,\kappa,p,q)}\Bigl[(T_{k/\kappa}w)(G)\ge\frac{\eta}{40\sqrt k}\Bigr]\ge\gamma.$$
--
--   An inverse-polynomial planted mean at size $k$ becomes, after vertex resampling, a constant-probability event at the larger planted size $\kappa$.
--
--   Differences from the source: none.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 6.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Resample

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 6.2, p.19 (PDF p.21).
Amplification of a nonnegative permutation-invariant statistic. `γ` and `N₀` come before `n, k, κ, w, η`. -/
theorem lemma_6_2 (p q A B τ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (hA : 0 < A) (hB : 0 < B)
    (hτ : 0 < τ) :
    ∃ (γ : ℝ) (N₀ : ℕ), 0 < γ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ n k κ : ℕ,
      (n : ℝ) ≤ (N : ℝ) ^ B → 1 ≤ k → (k : ℝ) ≤ (κ : ℝ) / 2 → (κ : ℝ) ≤ (n : ℝ) / 2 →
      (k : ℝ) / κ ≤ (N : ℝ) ^ (-τ) →
      ∀ w : Graph n → ℝ, (∀ G, 0 ≤ w G ∧ w G ≤ 1) → PermInvariant w →
      ∀ η : ℝ, η ≥ (N : ℝ) ^ (-A) → expect (pdsMass n k p q) w ≥ η →
        prob (pdsMass n κ p q)
          (fun G => resampleT q ((k : ℝ) / κ) w G ≥ η / (40 * Real.sqrt k)) ≥ γ := by sorry

end PDSEquiv

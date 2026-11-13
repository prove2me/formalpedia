-- Prove2me | Theorems.Thm_RestrictedAP_Counting_claim_5_14_monotone
-- name    : RestrictedAP.Counting.claim_5_14_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T16:14:44.157061+00:00
-- url     : https://prove2.me/theorems/34dacd6e-3f93-4d7f-9d69-e82ecab11f18
-- title:
--   Claim 5.14 with the hypothesis required at every density ≥ η (corrected: the printed hypothesis only constrains δ′ at exact densities)
-- statement:
--   **Source** (Claim 5.14, p. 32): in the setting of §5.2, if $\Delta_1(g)\ge\delta'(B,\eta)$ for every $(B,1/2)$-resilient $g:\Sigma^n\to\{0,1\}$ with $\eta=\nu^{\otimes n}(g)$, then $\Delta_1(f)\ge\alpha^{2B/(\delta\alpha^B)}\delta'(B,\delta)$ for every $f:\Sigma^n\to\{0,1\}$ with $\nu^{\otimes n}(f)=\delta$.
--
--   **Variant:** same setting ($\mu$ on $\Sigma^3$ with all marginals $\nu$, $(x,x,x)\in\mathrm{supp}(\mu)$ for all $x$, no $(\mathbb Z,+)$-embedding, $\alpha$ the minimum non-zero atom probability). If for every $\eta$ and every $(B,1/2)$-resilient $g:\Sigma^n\to\{0,1\}$ with $\nu^{\otimes n}(g)\ge\eta$ we have $\Delta_1(g)\ge\delta'(B,\eta)$, then for every $f:\Sigma^n\to\{0,1\}$ with $\nu^{\otimes n}(f)=\delta>0$,
--   $$\Delta_1(f)\ge\alpha^{2B/(\delta\alpha^B)}\,\delta'(B,\delta).$$
--
--   **Difference:** the hypothesis is required at every density $\ge\eta$, not only at the exact density $\eta=\nu^{\otimes n}(g)$. This is what the proof uses: it applies the hypothesis to the restriction $f_{I\to v}$, whose density is at least $\delta$ (not equal to it). Restrictions are functions on $\Sigma^n$ that ignore the coordinates in $I$, so a single dimension $n$ suffices; resilience of such a function on $\Sigma^n$ is resilience of $f_{I\to v}$ on $\Sigma^{\bar I}$.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 32, Claim 5.14 (corrected)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

namespace RestrictedAP.Counting

/-- Claim 5.14 with the hypothesis required at every density `≥ η` (corrected variant, INSIGHTS
I1): if `Δ₁(g) ≥ δ'(B, η)` for every `η` and every `(B, 1/2)`-resilient `g : Σ^n → {0,1}` with
`ν^{⊗n}(g) ≥ η`, then `Δ₁(f) ≥ α^{2B/(δ α^B)} δ'(B, δ)` for every `f : Σ^n → {0,1}` with
`ν^{⊗n}(f) = δ > 0`. -/
theorem claim_5_14_monotone (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (hμ : IsDist μ)
    (hmarg : ∀ i : Fin 3, marginal μ i = ν) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (hemb : ¬ DistHasEmbedding ℤ μ) (α : ℝ) (hα : IsMinAtom μ α)
    (n B : ℕ) (δ' : ℕ → ℝ → ℝ)
    (hyp : ∀ (η : ℝ) (g : (Fin n → Sig) → ℝ), (∀ x, g x = 0 ∨ g x = 1) →
      Resilient ν B (1 / 2) g → η ≤ expect (tensorPow ν n) g → δ' B η ≤ Delta1 μ g)
    (f : (Fin n → Sig) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hδ : 0 < expect (tensorPow ν n) f) :
    α ^ (2 * (B : ℝ) / (expect (tensorPow ν n) f * α ^ B)) *
        δ' B (expect (tensorPow ν n) f) ≤ Delta1 μ f := by sorry

end RestrictedAP.Counting

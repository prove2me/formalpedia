-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_theorem_2_1
-- name    : RelaxedPRS.StrongCvx.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:38.081859+00:00
-- url     : https://prove2.me/theorems/e54fb362-2a21-4672-a377-efdc6ec38007
-- title:
--   Theorem 2.1 — auxiliary-term bounds and best-iterate, ergodic, and nonergodic rates
-- statement:
--   Let $f,g$ be closed, proper, convex functions on a real Hilbert space, $\gamma>0$, and $(z^k)$ a relaxed PRS run with $\lambda_k\in(0,1]$. Let $z^*$ be a PRS fixed point and $x^*=\operatorname{prox}_{\gamma g}(z^*)$. With the paper's strong-convexity and gradient regularity terms $S_f,S_g$, every $k\ge0$ satisfies
--   $$8\gamma\lambda_k(S_f(x_f^k,x^*)+S_g(x_g^k,x^*))\le\|z^k-z^*\|^2-\|z^{k+1}-z^*\|^2+\left(1-\frac1{\lambda_k}\right)\|z^{k+1}-z^k\|^2.$$
--   Consequently, the weighted sum of these nonnegative terms is finite and at most $\|z^0-z^*\|^2/(8\gamma)$. If the $\lambda_j$ are bounded below by a positive constant, the best values of each term through $k$ are $o(1/(k+1))$. Their $\lambda_i$-weighted ergodic averages obey an $O(1/\Lambda_k)$ bound with the exact constant $\|z^0-z^*\|^2/(8\gamma\Lambda_k)$. If $\lambda_j(1-\lambda_j)$ are bounded below by a positive constant, the sum of the two last-iterate terms is $o(1/\sqrt{k+1})$.
--
--   This theorem collects the regularity estimates that the paper uses to obtain objective and fixed-point rates in its later sections.
--
--   **Formalization Note** The subgradients in $S_f,S_g$ are the particular proximal subgradients defined in Lemma 1.1. The ergodic subgradient averages carry the weights $\lambda_i$ matching the displayed averages of $x_f^i,x_g^i$; the unweighted repeated-$k$ gradient sum printed on p. 9 is a typographical slip.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, pp. 8–9, Theorem 2.1, (2.1)

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace
open Filter Asymptotics

namespace RelaxedPRS.StrongCvx

/-- Theorem 2.1, pp. 8–9, including (2.1), its infinite sum, and all three
convergence claims. The two ergodic subgradient averages are weighted by
`λ_i`, consistently with the weighted averages of the proximal points. -/
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f)
    (hlg : 0 < βg → HasLipGrad βg g)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : TPRS Pf Pg zs = zs) :
    let xs := xg Pg zs
    let Sf : ℕ → ℝ := fun k =>
      auxS μf βf (xf Pf Pg (z k)) xs (gtF γ Pf Pg (z k)) (gtF γ Pf Pg zs)
    let Sg : ℕ → ℝ := fun k =>
      auxS μg βg (xg Pg (z k)) xs (gtG γ Pg (z k)) (gtG γ Pg zs)
    let SbarF : ℕ → ℝ := fun k =>
      auxS μf βf
        (ergAvg lam (fun i => xf Pf Pg (z i)) k) xs
        (ergAvg lam (fun i => gtF γ Pf Pg (z i)) k) (gtF γ Pf Pg zs)
    let SbarG : ℕ → ℝ := fun k =>
      auxS μg βg
        (ergAvg lam (fun i => xg Pg (z i)) k) xs
        (ergAvg lam (fun i => gtG γ Pg (z i)) k) (gtG γ Pg zs)
    (∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 +
        (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2) ∧
    Summable (fun i => lam i * (Sf i + Sg i)) ∧
    8 * γ * (∑' i, lam i * (Sf i + Sg i)) ≤ ‖z 0 - zs‖ ^ 2 ∧
    ((∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ lam j) →
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sf) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sg) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1))) ∧
    (∀ k, SbarF k + SbarG k ≤
      ‖z 0 - zs‖ ^ 2 / (8 * γ * Lam lam k)) ∧
    ((∃ τ : ℝ, 0 < τ ∧ ∀ j, τ ≤ lam j * (1 - lam j)) →
      (fun k : ℕ => Sf k + Sg k) =o[Filter.atTop]
        (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1))) := by sorry

end RelaxedPRS.StrongCvx

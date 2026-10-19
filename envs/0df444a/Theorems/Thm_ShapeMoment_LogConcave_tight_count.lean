-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_tight_count
-- name    : ShapeMoment.LogConcave.tight_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:47.827111+00:00
-- url     : https://prove2.me/theorems/6e7cec22-d6e3-4323-8d91-aa0fd59a3d89
-- title:
--   Proof of Theorem 4.1 — tight LC constraints
-- statement:
--   Let $x^*$ be an optimal extreme point of (DMP-LC) with support $[k,\ell]$ and $q_0=1$. Then
--
--   $$(\ell-k+1)-(m+1)\le\#\{j:k<j<\ell,\ x^*_{j-1}x^*_{j+1}=(x^*_j)^2\}.$$
--
--   This counts tight interior log-concavity constraints. **Formalization Note** Natural-number subtraction makes the lower bound zero on short supports, the easy case discussed on page 14.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 15, proof of Theorem 4.1, tight-count step

import Definitions.Def_ShapeMoment_LogConcave_Model

namespace ShapeMoment.LogConcave

theorem tight_count (n m : ℕ) (q : ℕ → ℝ) (f : Fin n → ℝ)
    (hq0 : q 0 = 1) (x : Fin n → ℝ)
    (hext : x ∈ (feasLC n m q).extremePoints ℝ)
    (hopt : IsMaxSol f (feasLC n m q) x)
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkle : k ≤ ℓ) (hle : ℓ ≤ n)
    (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) :
    (ℓ - k + 1) - (m + 1) ≤
      ((Finset.Ioo k ℓ).filter
        (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2)).card := by sorry

end ShapeMoment.LogConcave

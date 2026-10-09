-- Prove2me | Theorems.Thm_SphereSOS_Rate_lamMax_toep_ge
-- name    : SphereSOS.Rate.lamMax_toep_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:41.897709+00:00
-- url     : https://prove2.me/theorems/271ce7f4-c02f-4eda-b3c9-a76f11f5cbce
-- title:
--   Proof of Prop. 7, p. 9 — $\lambda_{\max}(\mathcal T[h])\ge\lambda_{\max}(\mathcal T[\bar h])=\bar h(x_{\ell+1,\ell+1})$, $\bar h(t)=h'(1)(t-1)+h(1)$
-- statement:
--   Let $d\ge2$, $n\ge1$, $\ell\ge0$, $h=\frac1n\sum_{k=1}^nC_{2k}/C_{2k}(1)$ and $\bar h(t)=h'(1)(t-1)+h(1)$. For every root $x$ of the Gegenbauer polynomial $C_{\ell+1}$,
--   $$\lambda_{\max}\big(\mathcal T[h]\big)\ \ge\ \bar h(x)=h'(1)(x-1)+h(1).$$
--   In particular, at the largest root $x_{\ell+1,\ell+1}$ this is $\lambda_{\max}(\mathcal T[h])\ge\lambda_{\max}(\mathcal T[\bar h])=\bar h(x_{\ell+1,\ell+1})$.
--
--   Together with a lower bound on the largest root of $C_{\ell+1}$, this bounds $\tilde\rho_{2n}(d,\ell)=n-n\lambda_{\max}(\mathcal T[h])$ from above.
--
--   **Formalization Note** Stated for every root of $C_{\ell+1}$ (equivalently of $P_{\ell+1}$), which is equivalent to the statement at the largest root because $h'(1)>0$. Proposition 7 itself, $\lambda_{\max}(\mathcal T[h])\ge1-\frac{7n}{12}\frac{d^2}{\ell^2}$, is false as printed for small $d$ (e.g. $d=2$, $n=1$, $\ell=10$), as is the root bound $x_{\ell+1,\ell+1}\ge1-d^2/(4\ell^2)$ it quotes; neither is part of this statement.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 9, proof of Proposition 7, the paragraph 'It is easy to check …' and the first inequality of the final display

import Mathlib
import Definitions.Def_SphereSOS_Rate_Toeplitz

namespace SphereSOS.Rate

theorem lamMax_toep_ge (d n ℓ : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    ∀ x : ℝ, (geg d (ℓ + 1)).IsRoot x →
      (hpoly d n).derivative.eval 1 * (x - 1) + (hpoly d n).eval 1 ≤
        lamMax (toep d ℓ (fun t => (hpoly d n).eval t)) := by sorry

end SphereSOS.Rate

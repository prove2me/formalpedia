-- Prove2me | Theorems.Thm_TractableDRO_MeanCov_theorem_2_tight
-- name    : TractableDRO.MeanCov.theorem_2_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:35.229656+00:00
-- url     : https://prove2.me/theorems/95ab75e4-5389-47ac-8508-a6d6d791b759
-- title:
--   Theorem 2, p. 910 (tightness part) — π²(r⁰, r) ≤ sup over 𝔽₂ of E_ℙ((r⁰ + r′ζ̃)⁺)
-- statement:
--   Let $F \in \mathbb R^{N\times n}$ have full row rank, let $\Sigma \in \mathbb R^{N \times N}$ be symmetric positive semidefinite, let $\hat{\mathcal V} \subseteq \mathbb R^{n}$ be nonempty, and let $r^0 \in \mathbb R$, $r \in \mathbb R^{n}$. With $\mathbb F_2$ the family of distributions of $\tilde\zeta$ with finite second moments, mean in $\hat{\mathcal V}$ and $E_{\mathbb P}(F(\tilde\zeta - \hat\zeta)(\tilde\zeta - \hat\zeta)'F') = \Sigma$,
--
--   $$\pi^2(r^0, r) \le \sup_{\mathbb P \in \mathbb F_2} E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big).$$
--
--   In particular, when $F'y = r$ has no solution, the worst-case expectation is $+\infty$.
--
--   This is the tightness half of Theorem 2: no smaller bound depending only on the mean set and the covariance is valid.
--
--   **Formalization Note** The three hypotheses are implicit in the paper's model: $\Sigma$ is a covariance matrix (p. 905); $F$ "has to be full rank" (p. 906, after (9)), expressed as surjectivity of $x \mapsto Fx$; and the mean set is nonempty. Without any one of them $\mathbb F_2$ can be empty while $\pi^2$ is finite or $+\infty$. Both sides are extended reals.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Theorem 2 and (22); p. 906 (F full rank)

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem theorem_2_tight {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ))
    (hV : Vhat.Nonempty) (hSig : Sig.PosSemidef) (hF : Function.Surjective F.mulVec)
    (r0 : ℝ) (r : Fin n → ℝ) :
    pi2 F Sig Vhat r0 r ≤ TractableDRO.MeanSupport.worstCase (family2 F Sig Vhat) r0 r := by sorry

end TractableDRO.MeanCov

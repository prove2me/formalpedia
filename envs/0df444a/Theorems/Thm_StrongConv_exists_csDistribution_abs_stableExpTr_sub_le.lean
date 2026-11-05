-- Prove2me | Theorems.Thm_StrongConv_exists_csDistribution_abs_stableExpTr_sub_le
-- name    : StrongConv.exists_csDistribution_abs_stableExpTr_sub_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T00:05:07.843686+00:00
-- url     : https://prove2.me/theorems/a5c262c9-1a50-440b-aa4f-a8dd5ef9df4d
-- title:
--   Lemma 10.3 — expansion of the stable-representation trace of h(P(Πᴺ, Πᴺ*)) to order α
-- statement:
--   Fix a stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13, `StrongConv.StableRep`), with $D_N = \dim V_N$ and $\alpha = \deg_N D_N$ (`StrongConv.StableRep.alpha`). There is a constant $C$, depending only on $\pi$, such that for every $d \ge 2$, every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$ and $K = \|P\|_{\mathrm M_D(\mathbb C) \otimes C^*(\mathbf F_d)}$, there are compactly supported distributions $\nu_0, \nu_1, \dots$ (Definition 4.6) such that, for all $N \ge \max(N_0, 1)$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$,
--   $$\Big|\mathbf E\Big[\tfrac{1}{N^\alpha}\,\mathrm{Re}\,\mathrm{Tr}\, h\big(P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\big)\Big] - \sum_{i=0}^{\alpha} \frac{\nu_i(h)}{N^i}\Big| \le \frac{C\,D\,(q_0(1 + \log d))^{4(\alpha+1)}}{N^{\alpha+1}}\;\beta_*\,\big\|f^{(4(\alpha+1)+1)}\big\|_{L^\beta[0, 2\pi]},$$
--   where $f(\theta) = h(K\cos\theta)$, $1/\beta_* = 1 - 1/\beta$ and $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ for i.i.d. uniform $\sigma_i \in \mathbf S_N$. Here $\mathrm{Tr}$ is the trace on the $D D_N$-dimensional space $\mathbb C^D \otimes V_N$ and $h(T)$ is the functional calculus applied to $z \mapsto h(\mathrm{Re}\, z)$.
--
--   This is the statement of Lemma 10.3 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 32) in the form used by `StrongConv.prob_norm_eval_stableRep_ge_le`. The trace is normalized by $N^\alpha$ as in the paper, so the left side is of order $D$; the constant carries the factor $(1 + \log d)$ in place of $\log d$, which differs from the printed one by a constant factor for $d \ge 2$. The paper proves it by repeating sections 6 and 7 with the rationality of Lemma 10.1.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 32, Lemma 10.3

import Mathlib
import Definitions.Def_StrongConv

open Polynomial Filter Topology

namespace StrongConv

theorem exists_csDistribution_abs_stableExpTr_sub_le (π : StableRep) :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ}, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
        ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
                ((fnCalc (h : ℝ → ℝ) (P.eval (π.model σ)) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
                (N : ℝ) ^ π.alpha) -
            ∑ i ∈ Finset.range (π.alpha + 1), ν i h / (N : ℝ) ^ i| ≤
          C * D * (q₀ * (1 + Real.log d)) ^ (4 * (π.alpha + 1)) / (N : ℝ) ^ (π.alpha + 1) *
            conjExp β * lpNormCircle β (iteratedDeriv (4 * (π.alpha + 1) + 1)
              (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  sorry

end StrongConv

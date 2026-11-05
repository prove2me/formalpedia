-- Prove2me | Theorems.Thm_StrongConv_tendsto_prob_norm_trace_sub_trTau_ge
-- name    : StrongConv.tendsto_prob_norm_trace_sub_trTau_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T00:05:07.122257+00:00
-- url     : https://prove2.me/theorems/810abbb6-2c6b-40f0-b003-ee203f42eb4d
-- title:
--   Lemma A.2 — weak convergence in probability for stable representations
-- statement:
--   Fix a stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13, `StrongConv.StableRep`) with no copy of the trivial representation and $D_N \ge 1$ for $N \ge N_0$. Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be self-adjoint. For every $\eta > 0$,
--   $$\mathbf P\Big[\Big|\frac{\mathrm{Tr}\, P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})}{D\,D_N} - (\mathrm{tr}_D \otimes \tau)\big(P(\boldsymbol s, \boldsymbol s^*)\big)\Big| \ge \eta\Big] \to 0 \quad (N \to \infty),$$
--   where $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ for i.i.d. uniform $\sigma_i \in \mathbf S_N$, $\mathrm{Tr}$ is the (complex) trace on $\mathbb C^D \otimes V_N$, and $\mathrm{tr}_D \otimes \tau$ is `StrongConv.trTau`.
--
--   This is Lemma A.2 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 33), “$\mathrm{tr}_{DD_N}(P(\Pi^N, \Pi^{N*})) = (\mathrm{tr}_D \otimes \tau)(P(s, s^*)) + o(1)$ with probability $1 - o(1)$”, with the $o(1)$ terms written out. The hypothesis $D_N \ge 1$ is the one of Theorem A.1 in the mission. The paper reduces to irreducible stable representations through [32, Proposition B.2], to $D = 1$ through the diagonal blocks, and obtains the variance bound from Schur's lemma and the convergence in expectation (A.1) that follows from Lemma 10.2.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 33, Lemma A.2

import Mathlib
import Definitions.Def_StrongConv

open Polynomial Filter Topology

namespace StrongConv

theorem tendsto_prob_norm_trace_sub_trTau_ge (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      η ≤ ‖LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((P.eval (π.model σ) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) /
          ((D : ℂ) * (π.dim N : ℂ)) - trTau (P.eval (sLimit d))‖))
      atTop (𝓝 0) := by
  sorry

end StrongConv

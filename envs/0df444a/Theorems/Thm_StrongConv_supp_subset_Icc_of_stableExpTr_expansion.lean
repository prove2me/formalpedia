-- Prove2me | Theorems.Thm_StrongConv_supp_subset_Icc_of_stableExpTr_expansion
-- name    : StrongConv.supp_subset_Icc_of_stableExpTr_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T00:05:05.957279+00:00
-- url     : https://prove2.me/theorems/3f24a409-57f0-4fc3-a0dc-96e02fcde476
-- title:
--   Lemma 10.4 — supp νᵢ ⊆ [−‖P(s, s*)‖, ‖P(s, s*)‖] for i ≤ α
-- statement:
--   Fix a stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13, `StrongConv.StableRep`) with no copy of the trivial representation, $d \ge 2$, and a self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$. Let $\nu_0, \nu_1, \dots$ be compactly supported distributions (Definition 4.6) such that, for every real polynomial $h$, there is $C_h$ with
--   $$\Big|\mathbf E\Big[\tfrac{1}{N^\alpha}\,\mathrm{Re}\,\mathrm{Tr}\, h\big(P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\big)\Big] - \sum_{i=0}^{\alpha} \frac{\nu_i(h)}{N^i}\Big| \le \frac{C_h}{N^{\alpha+1}} \quad \text{for all } N \ge \max(N_0, 1).$$
--   Then $\operatorname{supp}\nu_i \subseteq [-\|P(\boldsymbol s, \boldsymbol s^*)\|, \|P(\boldsymbol s, \boldsymbol s^*)\|]$ for $i = 0, \dots, \alpha$ (support as in Definition 4.8, `StrongConv.supp`).
--
--   This is Lemma 10.4 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 32). The paper leaves implicit that the $\nu_i$ are the ones of Lemma 10.3; a compactly supported distribution is determined by its values on polynomials, so the hypothesis above pins down $\nu_0, \dots, \nu_\alpha$ and the statement here applies to any distributions with this expansion. The paper's proof uses the limits of Lemma 10.2 for $i < \alpha$ and, for $i = \alpha$, the representation of $\nu_\alpha(x^p)$ together with Lemmas 9.6 and 4.9.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 32, Lemma 10.4

import Mathlib
import Definitions.Def_StrongConv

open Polynomial Filter Topology

namespace StrongConv

theorem supp_subset_Icc_of_stableExpTr_expansion (π : StableRep) (hπ : π.NoTrivialSummand)
    {D d : ℕ} (hd : 2 ≤ d) (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (ν : ℕ → smoothFun →ₗ[ℝ] ℝ) (hν : ∀ i, IsCSDistribution (ν i))
    (hexp : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((fnCalc (fun x => h.eval x) (P.eval (π.model σ)) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
            (N : ℝ) ^ π.alpha) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1)) :
    ∀ i ≤ π.alpha, supp (ν i) ⊆
      Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ := by
  sorry

end StrongConv

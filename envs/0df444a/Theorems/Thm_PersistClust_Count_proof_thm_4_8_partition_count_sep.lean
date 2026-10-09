-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_sep
-- name    : PersistClust.Count.proof_thm_4_8_partition_count_sep
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T10:09:49.096465+00:00
-- url     : https://prove2.me/theorems/fc8b93bb-e668-4cca-b3af-37eede294b3c
-- title:
--   Thm 4.8 counting, step 1: $d_2$-prominent part equals $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ (separation)
-- statement:
--   Let $D : \mathbb{E}^2 \to \mathbb{N} \cup \{\infty\}$ be a persistence diagram that is $(d_1, d_2)$-separated with $d_1 < d_2$: every off-diagonal point of $D$ lies in the open half-plane $\Delta^N_{d_1}$ (death exceeding birth minus $d_1$) or in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ (death at most birth minus $d_2$ and birth exceeding $d_2$). Then the total multiplicity of $D$ in the closed half-plane $\Delta^S_{d_2}$ — the number $\mathrm{prominentCount}(D, d_2)$ of points of $D$ with prominence (birth minus death) at least $d_2$ — equals the total multiplicity of $D$ in the smaller region $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$. Indeed, a point of $\Delta^S_{d_2}$ cannot lie in $\Delta^N_{d_1}$, since that would force $d_2 < d_1$, contradicting $d_1 < d_2$; so by separation it lies in the $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ branch. This is the source-side set equality of the counting step in the proof of Theorem 4.8: the $d_2$-prominent part $D_2$ of the diagram consists exactly of the points in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$.
-- source:
--   Chazal, Guibas, Oudot, Skraba: Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report RR-6968, 2009, p. 22, proof of Theorem 4.8 (counting part); https://hal.inria.fr/inria-00389390

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

theorem proof_thm_4_8_partition_count_sep
    (D : EReal × EReal → ℕ∞) (hD : IsDiagramLike D)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hsep : IsSeparated D d₁ d₂) (hd12 : d₁ < d₂) :
    prominentCount D d₂ =
      {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard := by sorry

end PersistClust.Count

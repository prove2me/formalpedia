-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_transport
-- name    : PersistClust.Count.proof_thm_4_8_partition_count_transport
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T10:10:11.37216+00:00
-- url     : https://prove2.me/theorems/fa8eac3e-0648-48e8-958f-e6166266b0fc
-- title:
--   Thm 4.8 counting, step 2: $\gamma$ transports $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ to the $\tau$-window
-- statement:
--   Let $D, D'$ be persistence diagrams off the diagonal and let $\gamma : \mathrm{Copies}(D) \simeq \mathrm{Copies}(D')$ be a multi-bijection of their copies satisfying assertions (i)–(iv) of Theorem 4.5 with threshold $\alpha = c\delta$ and radius $c\delta$: points of $Q^{NE}_{c\delta}$ have both coordinates $c\delta$-close to their images and preimages, and points of $Q^{SE}_{c\delta}$ have their birth coordinate $c\delta$-close to their images and preimages. Assume $D$ is $(d_1, d_2)$-separated with $\delta < (d_2 - d_1)/(5c)$ and let $\tau$ lie in the window $d_1 + 2c\delta < \tau < d_2 - 3c\delta$. Then the total multiplicity of $D$ in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ equals the total multiplicity of $D'$ in $\Delta^S_{\tau} \cap \Lambda^E_{\tau}$. The reason is that $\gamma$ restricts to a bijection between these two sets of copies: in one direction, the five-region analysis of the proof of Theorem 4.8 (regions III–V) shows that a copy of $D$ whose point lies in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$ is sent to a copy of $D'$ whose point lies in $\Delta^S_{\tau} \cap \Lambda^E_{\tau}$; in the other direction, a copy of $D'$ in $\Delta^S_{\tau} \cap \Lambda^E_{\tau}$ is sent back to a copy of $D$ whose point, by separation, cannot lie in $\Delta^N_{d_1}$ (its prominence exceeds $\tau - 2c\delta > d_1$ by the $c\delta$-closeness), hence lies in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$. Both sets are off the diagonal since $0 < d_2$ and $0 < \tau$.
-- source:
--   Chazal, Guibas, Oudot, Skraba: Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report RR-6968, 2009, p. 22, proof of Theorem 4.8 (counting part); https://hal.inria.fr/inria-00389390

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

theorem proof_thm_4_8_partition_count_transport
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard := by sorry

end PersistClust.Count

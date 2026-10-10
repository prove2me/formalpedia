-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_transport_reverse
-- name    : PersistClust.Count.proof_thm_4_8_partition_count_transport_reverse
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T12:06:07.51523+00:00
-- url     : https://prove2.me/theorems/27b47b83-d428-4790-ba23-7b2aa0f3e0cb
-- title:
--   Reverse bound: $\tau$-window copies of $D'$ inject into copies of $D$ of prominence $\ge d_2$
-- statement:
--   Let $D$ and $D'$ be persistence diagrams in the extended plane $\overline{\mathbb{R}} \times \overline{\mathbb{R}}$, i.e. multiplicity functions $D, D' : \overline{\mathbb{R}} \times \overline{\mathbb{R}} \to \mathbb{N} \cup \{\infty\}$ that are diagram-like: every point $(b,d)$ of positive multiplicity lies strictly off the diagonal, $d < b$. Write $\operatorname{Copies}(D)$ for the multiset of copies of $D$: for each point $p$ it contains $D(p)$ copies $(p,k)$, $k < D(p)$, together with countably many copies of every diagonal point.
--
--   Let $\gamma : \operatorname{Copies}(D) \simeq \operatorname{Copies}(D')$ be a multi-bijection (a bijection of copies) satisfying assertions (i)–(iv) of Theorem 4.5 of the source paper at threshold $\alpha = c\delta$ and radius $r = c\delta$: whenever the point of a copy lies in the quadrant $Q^{NE}_\alpha$ (both coordinates $> \alpha$), both coordinates of the point of the matched copy — in either direction of $\gamma$ — are within $r$ in the sense that $x \le x' + r$ and $x' \le x + r$ in the extended reals ($\pm\infty$ being close only to itself); whenever the point of a copy lies in the quadrant $Q^{SE}_\alpha$ (first coordinate $> \alpha$, second coordinate $\le \alpha$), only the first coordinate of the matched point is guaranteed within $r$, again in either direction.
--
--   Fix real numbers $c > 0$, $\delta > 0$, $0 \le d_1$ and $d_2$ with $\delta < (d_2 - d_1)/(5c)$, i.e. $5c\delta < d_2 - d_1$, and a window point $\tau$ with $d_1 + 2c\delta < \tau < d_2 - 3c\delta$. Assume $D$ is $(d_1, d_2)$-separated: every point of $D$ of positive multiplicity lies in the open half-plane $\Delta^N_{d_1}$ above the line $y = x - d_1$, or in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$, where $\Delta^S_d = \{(x,y) : y \le x - d\}$ is the closed half-plane of prominence at least $d$, $\Delta^N_d$ is its open complement, and $\Lambda^E_d = \{(x,y) : d < x\}$ is the open half-plane of births above $d$.
--
--   This lemma is the reverse half of the equality that counts the copies of $D$ of prominence at least $d_2$ against the copies of $D'$ lying in the $\tau$-window:
--   $$\#\{(p,k) : k < D(p),\; p \in \Delta^S_{d_2} \cap \Lambda^E_{d_2}\} \;\ge\; \#\{(p,k) : k < D'(p),\; p \in \Delta^S_{\tau} \cap \Lambda^E_{\tau}\},$$
--   where both counts range over copies (a point together with an index below its multiplicity) and are computed as extended cardinalities of the corresponding copy sets.
--
--   The inequality is realized by the map sending a copy $(p,k)$ of $D'$ with $p \in \Delta^S_\tau \cap \Lambda^E_\tau$ to its preimage $\gamma^{-1}(p,k)$: assertions (i), (ii) and (iv) at threshold $c\delta$, together with the membership $p_2 \le p_1 - \tau$, force the preimage point $q$ to satisfy $q_2 \le q_1 - (\tau - 2c\delta)$, hence $q \notin \Delta^N_{d_1}$ because $d_1 + 2c\delta < \tau$; a diagonal preimage copy is excluded since its equal coordinates together with $p_2 \le p_1 - \tau$ would force $\tau \le 2c\delta$, contradicting $\tau > d_1 + 2c\delta \ge 2c\delta$. The preimage point carries a copy of $D$ and, since $D$ is $(d_1, d_2)$-separated and does not lie in $\Delta^N_{d_1}$, it must lie in $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$. Injectivity of $\gamma^{-1}$ makes the map injective.
--
--   **Formalization Note.** All notions live in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`): `Copies`, `pt`, `IsDiagramLike`, `SatisfiesIIV` (assertions (i)–(iv) via `closeE`, at threshold and radius `c * δ`), `IsSeparated`, and the regions `DeltaS d = {p | p.2 ≤ p.1 - ↑d}` (closed) and `LamE d = {p | ↑d < p.1}` (open). The count is `Set.encard` of the set of copies $q = (p,k)$ with the natural-number index $k$ coerced into $\mathbb{N} \cup \{\infty\}$ and compared strictly against the multiplicity at $p$.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), §4.2, proof of Theorem 4.8 (pp. 22–23): reverse half of the transport of the $d_2$-prominence count of $D$ to the $\tau$-window count of $D'$ along the multi-bijection $\gamma$ of Theorem 4.5 (separation into $\Delta^N_{d_1}$ versus $\Delta^S_{d_2} \cap \Lambda^E_{d_2}$).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count
theorem proof_thm_4_8_partition_count_transport_reverse
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard := by sorry
end PersistClust.Count
